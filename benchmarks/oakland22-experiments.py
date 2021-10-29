#!/usr/local/bin/python3

import os
import time
import csv
from subprocess import check_call, Popen, STDOUT

# CCS21 Experiments

OBLIVC_TESTS_DIR = "/Users/ian/Projects/obliv-c-extra/test/oblivc"
ALLYN_DIR = "/Users/ian/Projects/allyn-lang"
ALLYN_INPUTS_DIR = "{0}/{1}".format(ALLYN_DIR, "examples-input")

GATE_COUNT_F = "gate_count.txt"

DEVNULL = open(os.devnull, 'wb', 0)

def run_and_measure(cmd, procs):
    start = time.perf_counter()
    check_call(cmd, stdout=DEVNULL, stderr=STDOUT)
    for p in procs:
        p.wait()
    stop = time.perf_counter()
    return stop - start

def gate_count(cmd, procs):
    if os.path.exists(GATE_COUNT_F):
        os.remove(GATE_COUNT_F)
    check_call(cmd, stdout=DEVNULL, stderr=STDOUT)
    for p in procs:
        p.wait()
    with open(GATE_COUNT_F, 'r') as f:
        return list(map(int, f.read().split()))

def just_run(cmd):
    return Popen(cmd, stdout=DEVNULL, stderr=STDOUT)

def to_csv(f,fields,data):
    with open(f, 'w', newline='') as f:
        w = csv.DictWriter(f,fields)
        w.writeheader()
        for sample in data:
            w.writerow(sample)

def make_allyn(name, protocol, size):
    template_path = "{0}/examples/templates/{1}-template.all".format(ALLYN_DIR, name)
    dest_path = "{0}/examples/{1}-{2}-{3}.all".format(ALLYN_DIR, name, protocol, size)
    with open(template_path, 'r') as template:
        with open(dest_path, 'w') as dest:
            dest.write(template.read().format(protocol, size))

def make_repeat_input(name, party, size):
    template_path = "{0}/examples-input/{1}/templates/{2}-input-template.txt".format(ALLYN_DIR, party, name)
    dest_path = "{0}/examples-input/{1}/{2}-input-{3}.txt".format(ALLYN_DIR, party, name, size)
    with open(template_path, 'r') as template:
        with open(dest_path, 'w') as dest:
            inp_template  = template.read()
            size_template = inp_template.count('\n')
            n = int(size / size_template)
            dest.write(str(size) + '\n')
            for _ in range(n):
                dest.write(inp_template)

def make_identical_input(name, party, size):
    template_path = "{0}/examples-input/{1}/templates/{2}-input-template.txt".format(ALLYN_DIR, party, name)
    dest_path = "{0}/examples-input/{1}/{2}-input-{3}.txt".format(ALLYN_DIR, party, name, size)
    with open(template_path, 'r') as template:
        with open(dest_path, 'w') as dest:
            inp_template  = template.read()
            dest.write(inp_template)

def make_gcd_input(party, size):
    dest_path = "{0}/examples-input/{1}/gcd-gc-input-{2}.txt".format(ALLYN_DIR, party, size)
    with open(dest_path, 'w') as dest:
        dest.write(str(size) + '\n')

def make_hamming_list(protocol, size):
    make_allyn("hamming-list", protocol, size)
    make_repeat_input("hamming-list", "A", size)
    make_repeat_input("hamming-list", "B", size)

def make_hamming(protocol, size):
    make_allyn("hamming", protocol, size)
    make_repeat_input("hamming", "A", size)
    make_repeat_input("hamming", "B", size)

def make_bio_matching(protocol, size):
    make_allyn("bio-matching", protocol, size)
    make_repeat_input("bio-matching", "A", size)
    make_identical_input("bio-matching", "B", size)

def make_db_analytics(protocol, size):
    make_allyn("db-analytics", protocol, size)
    make_repeat_input("db-analytics", "A", size)
    make_repeat_input("db-analytics", "B", size)

def make_gcd_gc(protocol, size):
    make_allyn("gcd-gc", protocol, size)
    make_gcd_input("A", size)
    make_gcd_input("B", size)


def make_edit_distance(protocol, size):
    make_allyn("edit-distance", protocol, size)
    make_repeat_input("edit-distance", "A", size)
    make_repeat_input("edit-distance", "B", size)

## For each implementation...
impls = [ "allyn", "oblivc" ]

## ...and each possible protocol...
protocols = [ "yao", "plain" ]

## ...run the following benchmarks...
benchmarks = [ ("hamming",       [ "A", "B" ], [ 10000, 20000, 30000, 40000, 50000 ], make_hamming)
             , ("bio-matching",  [ "A", "B" ], [ 100, 200, 300, 400, 500 ], make_bio_matching)
             , ("db-analytics",  [ "A", "B" ], [ 60, 70, 80, 90, 100 ], make_db_analytics)
             , ("gcd-gc",        [ "A", "B" ], [ 500, 600, 700, 800, 900 ], make_gcd_gc)
             , ("edit-distance", [ "A", "B" ], [ 50, 80, 110, 140, 170 ], make_edit_distance) #TODO(ins): k-means, karmakar, guassian elimination, psi
             ]

## ...and take this many samples.
num_runs = 5

### Run a benchmark
def benchmark_parties(mkCmd, parties, sampler):
    procs = []
    for party in parties[1:]:
        cmd = mkCmd(party)
        procs.append(just_run(cmd))
    cmd = mkCmd(parties[0])
    elapsed = sampler(cmd, procs)
    print ("{0} --> {1}".format(" ".join(cmd), elapsed))
    return elapsed

## Run an end-to-end benchmark in PSL
def benchmark_allyn(protocol, name, size, parties, sampler):
    benchmark = "{0}-{1}-{2}".format(name, protocol, size)
    mkCmd = lambda party : [ "./allyn", "example", "-P", party, benchmark ]
    return benchmark_parties(mkCmd, parties, sampler)

## Run an end-to-end benchmark in OblivC
def benchmark_oblivc(protocol, name, size, parties, sampler):
    executable = "{0}/{1}/a.out".format(OBLIVC_TESTS_DIR, name)
    plain_flag = [ "-p" ] if protocol == "plain" else [ ]
    mkCmd = lambda party : [ executable, "-P", party, "-i", "{0}/{1}/{2}-input-{3}.txt".format(ALLYN_INPUTS_DIR, party, name, size) ] + plain_flag
    return benchmark_parties(mkCmd, parties, sampler)

## Run an end-to-end benchmark using MPC
def run_sample(impl, protocol, benchmark_name, benchmark_size, benchmark_parties, sampler):
    if impl == "allyn":
        return benchmark_allyn(protocol, benchmark_name, benchmark_size, benchmark_parties, sampler)
    elif impl == "oblivc":
        return benchmark_oblivc(protocol, benchmark_name, benchmark_size, benchmark_parties, sampler)
    else:
        assert False, "Impossible."

def setup_benchmarks():
    for benchmark in benchmarks:
        for protocol in protocols:
            for sz in benchmark[2]:
                benchmark[3](protocol, sz)

### End-To-End Benchmarks
def end_to_end(f):
    data = [ ]
    for impl in impls:
        for protocol in protocols:
            for benchmark in benchmarks:
                for sz in benchmark[2]:
                    for r in range(num_runs):
                        sample = run_sample(impl, protocol, benchmark[0], sz, benchmark[1], run_and_measure)
                        data.append({ 'MPC Implementation' : impl,
                                      'Protocol'           : protocol,
                                      'Benchmark'          : benchmark[0],
                                      'Input Size'         : sz,
                                      'Elapsed Time (s)'   : sample })
    to_csv(f, [ 'MPC Implementation', 'Protocol', 'Benchmark', 'Input Size', 'Elapsed Time (s)' ], data)

### Gate Counts
def gates(f):
    data = [ ]
    for impl in impls:
        for benchmark in benchmarks:
            for sz in benchmark[2]:
                sample = run_sample(impl, "yao", benchmark[0], sz, benchmark[1], gate_count)
                data.append({ 'MPC Implementation' : impl,
                              'Benchmark'          : benchmark[0],
                              'Input Size'         : sz,
                              'AND gates'          : sample[0],
                              'XOR gates'          : sample[1] })
    to_csv(f, [ 'MPC Implementation', 'Benchmark', 'Input Size', 'AND gates', 'XOR gates' ], data)


def main():
    setup_benchmarks()
    print ("done setup")
    end_to_end('end-to-end.csv')
#    gates('gates.csv')

if __name__ == "__main__":
    main()
