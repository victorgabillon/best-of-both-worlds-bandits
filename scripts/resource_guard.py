#!/usr/bin/env python3
"""Portable process-group watchdog; established guard logic retained unchanged.

The caller supplies PROJECT (the repository root). Only the owned child group
can be stopped. Linux /proc watchdog, not an operating-system memory cap.
"""
from __future__ import annotations
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import sys
import time
PROJECT = Path(__file__).resolve().parents[1]
GIB = 1024**3
POLL_SECONDS = 0.2
CPU_SECONDS = 600
WALL_SECONDS = 900
MIN_AVAILABLE_BYTES = GIB

def now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()

def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()

def available_bytes() -> int:
    for line in Path("/proc/meminfo").read_text().splitlines():
        if line.startswith("MemAvailable:"):
            return int(line.split()[1]) * 1024
    raise RuntimeError("Linux MemAvailable is unavailable; refusing an unguarded run")

def atomic_json(path: Path, value: dict) -> None:
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)

def child_limits() -> None:
    resource.setrlimit(resource.RLIMIT_CPU, (CPU_SECONDS, CPU_SECONDS))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

def owned_rss(root_pid: int) -> int:
    """Sum current VmRSS for this child and its descendants, once per PID."""
    pending = [root_pid]
    seen = set()
    total = 0
    while pending:
        pid = pending.pop()
        if pid in seen:
            continue
        seen.add(pid)
        try:
            # Enumerate every thread's children: a multithreaded parent may spawn
            # a child from a thread other than its main thread.
            for task in (Path("/proc") / str(pid) / "task").iterdir():
                try:
                    pending.extend(int(n) for n in (task / "children").read_text().split())
                except (OSError, ValueError):
                    pass
            for line in (Path("/proc") / str(pid) / "status").read_text().splitlines():
                if line.startswith("VmRSS:"):
                    total += int(line.split()[1]) * 1024
                    break
        except (FileNotFoundError, ProcessLookupError):
            pass
    return total

def stop_owned_group(process: subprocess.Popen, immediate: bool = False) -> None:
    """The child uses start_new_session, so its PGID cannot include VS Code."""
    try:
        os.killpg(process.pid, signal.SIGKILL if immediate else signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        process.wait(timeout=2)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait()

def replay_module(item: dict, env: dict, log: Path, rss_limit: int, checkpoint) -> None:
    started = time.monotonic()
    process = None
    item.update(status="running", started_utc=now(), log=str(log), peak_sampled_group_rss_bytes=0)
    checkpoint()
    try:
        with log.open("w") as handle:
            handle.write("Command: " + " ".join(item["command"]) + "\n")
            handle.flush()
            process = subprocess.Popen(item["command"], cwd=PROJECT, env=env,
                                       stdin=subprocess.DEVNULL, stdout=handle,
                                       stderr=subprocess.STDOUT, start_new_session=True,
                                       preexec_fn=child_limits)
            item["owned_process_group"] = process.pid
            checkpoint()
            last_progress = started
            while process.poll() is None:
                rss = owned_rss(process.pid)
                item["peak_sampled_group_rss_bytes"] = max(item["peak_sampled_group_rss_bytes"], rss)
                elapsed = time.monotonic() - started
                reason = None
                if rss >= rss_limit:
                    reason = "aggregate owned-process RSS watchdog limit reached"
                elif available_bytes() < MIN_AVAILABLE_BYTES:
                    reason = "system MemAvailable fell below the 1 GiB safety floor"
                elif elapsed >= WALL_SECONDS:
                    reason = "per-module wall-clock limit reached"
                if reason:
                    item.update(status="stopped_by_guard", reason=reason)
                    stop_owned_group(process, immediate="RSS" in reason or "MemAvailable" in reason)
                    break
                if time.monotonic() - last_progress >= 30:
                    print(f"Running {item['module']}: {elapsed:.0f}s; group RSS {rss / GIB:.2f} GiB", flush=True)
                    checkpoint()
                    last_progress = time.monotonic()
                try:
                    process.wait(timeout=POLL_SECONDS)
                except subprocess.TimeoutExpired:
                    pass
            item["exit_code"] = process.wait()
            if item["status"] == "running":
                item["status"] = "passed" if item["exit_code"] == 0 else "failed"
    except BaseException:
        if process is not None:
            stop_owned_group(process)
            item["exit_code"] = process.returncode
        item["status"] = "cancelled" if isinstance(sys.exc_info()[1], KeyboardInterrupt) else "failed"
        raise
    finally:
        item.update(finished_utc=now(), elapsed_seconds=round(time.monotonic() - started, 3))
        checkpoint()
