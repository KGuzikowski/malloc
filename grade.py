#!/usr/bin/env python3

import signal
import subprocess
import sys


MINUTIL = 60
TIMEOUT = 30
TRACEFILES = [
        "traces/amptjp-bal.rep",
        "traces/amptjp.rep",
        "traces/bash.rep",
        "traces/binary.rep",
        "traces/binary-bal.rep",
        "traces/binary2.rep",
        "traces/binary2-bal.rep",
        "traces/cccp.rep",
        "traces/cccp-bal.rep",
        "traces/chrome.rep",
        "traces/coalescing.rep",
        "traces/coalescing-bal.rep",
        "traces/coalesce-big.rep",
        "traces/corners.rep",
        "traces/cp-decl.rep",
        "traces/cp-decl-bal.rep",
        "traces/expr.rep",
        "traces/expr-bal.rep",
        "traces/firefox.rep",
        "traces/fs.rep",
        "traces/hostname.rep",
        "traces/login.rep",
        "traces/lrucd.rep",
        "traces/ls.rep",
        "traces/ls.1.rep",
        "traces/malloc.rep",
        "traces/malloc-free.rep",
        "traces/nlydf.rep",
        "traces/perl.rep",
        "traces/perl.1.rep",
        "traces/perl.2.rep",
        "traces/perl.3.rep",
        "traces/pulseaudio.rep",
        "traces/qyqyc.rep",
        "traces/random.rep",
        "traces/random-bal.rep",
        "traces/random2.rep",
        "traces/random2-bal.rep",
        "traces/realloc2.rep",
        "traces/realloc2-bal.rep",
        "traces/rm.rep",
        "traces/rm.1.rep",
        "traces/rulsr.rep",
        "traces/short1.rep",
        "traces/short1-bal.rep",
        "traces/short2.rep",
        "traces/short2-bal.rep",
        "traces/stty.rep",
        "traces/tty.rep",
        "traces/xterm.rep"]

TRACEFILES_EXTRA = [
        "traces-private/alaska.rep",
        "traces-private/firefox-reddit2.rep",
        "traces-private/firefox-reddit.rep",
        "traces-private/freeciv.rep",
        "traces-private/merry-go-round.rep",
        "traces-private/realloc-bal.rep",
        "traces-private/realloc.rep",
        "traces-private/seglist.rep"]


def runtrace(trace):
    mdriver = subprocess.run([
        "valgrind",
        "--tool=callgrind",
        "--callgrind-out-file=callgrind.out",
        "--toggle-collect=mm_malloc",
        "--toggle-collect=mm_free",
        "--toggle-collect=mm_realloc",
        "--toggle-collect=mm_calloc",
        "--", "./mdriver", "-f", trace],
        capture_output=True, timeout=TIMEOUT)

    print(mdriver.stdout.decode())
    if mdriver.returncode:
        if mdriver.returncode < 0:
            signame = signal.Signals(-mdriver.returncode).name
            print("Your solution has been terminated by %s!" % signame)
        sys.exit(1)

    # Process statistics from mdriver
    stats = mdriver.stdout.decode().splitlines()[3][4:].split()
    try:
        util = float(stats[1][:-1])
    except ValueError:
        util = 0.0

    annotate = subprocess.run([
        "callgrind_annotate", "--tree=calling", "callgrind.out"],
        capture_output=True)

    # Process output from callgrind_annotate
    insn = 0
    show = 10000
    for i, line in enumerate(annotate.stdout.decode().splitlines()):
        if i >= show and line:
            print(line)
        if 'PROGRAM TOTALS' in line:
            insn = int(line.strip().split()[0].replace(',', ''))
        if 'file:function' in line:
            show = i + 3

    sys.stdout.flush()

    return util, insn


if __name__ == '__main__':
    all_ops = []
    all_insn = []
    all_util = []

    for trace in TRACEFILES:
        print("\nRunning mdriver for '%s'..." % trace)

        with open(trace, "r") as f:
            _ = int(f.readline())
            _ = int(f.readline())
            ops = int(f.readline())

        util = 0.0              # default utilization penalty for timeout
        insn = 50000.0 * ops    # default throughput penalty for timeout

        try:
            util, insn = runtrace(trace)
        except subprocess.TimeoutExpired:
            print("Penalty accrued for timeout of %ds." % TIMEOUT)

        all_insn.append(insn)
        all_util.append(util)
        all_ops.append(ops)

    # Grade solution
    weighted_util = 0
    for util, ops in zip(all_util, all_ops):
        weighted_util += util * (ops / sum(all_ops))

    print("\nWeighted memory utilization: %.1f%%" % weighted_util)
    print("Instructions per operation: %d" % (sum(all_insn) / sum(all_ops)))

    if weighted_util < MINUTIL:
        print("Minimum threshold for memory utilization "
              "of %d%% has not been met!" % MINUTIL)
        print("Your solution was disqualified! :(")
        sys.exit(1)
