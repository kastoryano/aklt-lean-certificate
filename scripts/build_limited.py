#!/usr/bin/env python3
"""Schedule project modules with bounded concurrency, then run the full Lake target."""
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from pathlib import Path
import os
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
SOURCES = {'.'.join(p.relative_to(ROOT).with_suffix('').parts): p
           for p in [ROOT / 'RootedKP.lean', *(ROOT / 'RootedKP').rglob('*.lean')]}
IMPORT = re.compile(r'^import\s+(RootedKP(?:\.[A-Za-z0-9_]+)*)\s*$', re.M)
DEPS = {name: set(IMPORT.findall(path.read_text())) for name, path in SOURCES.items()}
ORDER = []
ACTIVE = set()


def visit(name):
    if name in ORDER:
        return
    if name in ACTIVE:
        raise RuntimeError('Cyclic project import: ' + name)
    ACTIVE.add(name)
    for dep in sorted(DEPS[name]):
        visit(dep)
    ACTIVE.remove(name)
    ORDER.append(name)


def build(name):
    start = time.monotonic()
    env = dict(os.environ)
    env.setdefault('LEAN_NUM_THREADS', '1')
    result = subprocess.run([str(ROOT / 'scripts/lake.sh'), 'build', name],
                            cwd=ROOT, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    return name, result.returncode, result.stdout, time.monotonic() - start


def main():
    workers = int(os.environ.get('AKLT_BUILD_JOBS', '2'))
    if workers < 1:
        raise ValueError('AKLT_BUILD_JOBS must be a positive integer')
    # Let Lake validate an existing cache before scheduling each module.
    # --no-build checks freshness and cannot launch an unbounded cold build.
    cached = subprocess.run([str(ROOT / 'scripts/lake.sh'), '--no-build', 'build'],
                            cwd=ROOT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    if cached.returncode == 0:
        print(cached.stdout, end='', flush=True)
        print('Lake validated the existing project build cache.', flush=True)
        return 0
    visit('RootedKP')
    remaining = set(ORDER)
    done = set()
    start = time.monotonic()
    print(f'Checking {len(ORDER)} project modules with at most {workers} workers.', flush=True)
    with ThreadPoolExecutor(max_workers=workers) as pool:
        running = {}
        while remaining or running:
            for name in ORDER:
                if len(running) >= workers:
                    break
                if name in remaining and DEPS[name] <= done:
                    remaining.remove(name)
                    running[pool.submit(build, name)] = name
            if not running:
                raise RuntimeError('No buildable module remains')
            completed, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in completed:
                del running[future]
                name, status, output, elapsed = future.result()
                if status:
                    print(output, flush=True)
                    print(f'FAILED: {name}', flush=True)
                    return status
                done.add(name)
                print(f'[{len(done)}/{len(ORDER)}] {name}: {elapsed:.1f}s', flush=True)
    # Lake remains authoritative about the full target and import graph.
    result = subprocess.run([str(ROOT / 'scripts/lake.sh'), 'build'], cwd=ROOT)
    print(f'Total project build time: {time.monotonic() - start:.1f}s', flush=True)
    return result.returncode


if __name__ == '__main__':
    sys.exit(main())
