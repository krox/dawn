#!/usr/bin/env python3
from subprocess import call
from sys import argv

for i in range(0, 10000):
    print("fuzzing seed", i)
    cnfFile = open('tmp.cnf', 'w')
    logFile = open('tmp.log', 'w')

    if len(argv) >= 2:
        mode = int(argv[1])
    else:
        mode = 1

    if mode == 1:
        cmd = ['../cnf-utils/cnf-fuzz-biere', str(i)]
    elif mode == 2:
        cmd = ['../cnf-utils/cnf-fuzz-brummayer.py', '-s', str(i)]
    elif mode == 3:
        cmd = ['../cnf-utils/cnf-fuzz-xor.py', '--seed=' + str(i)]
    elif mode == 4:
        cmd = ['../cnf-utils/largefuzzer', str(i)]
    elif mode == 5:
        cmd = ['../cnf-utils/sgen4', '-n', '100', '-sat', '-s', str(i)]
    elif mode == 6:
        cmd = ['../cnf-utils/sgen4', '-n', '50', '-unsat', '-s', str(i)]
    else:
        raise "invalid mode"

    r = call(cmd, stdout=cnfFile)
    if r != 0:
        raise "fuzzer failed"
    cnfFile.close()

    r = call(['build/dawn', 'solve', 'tmp.cnf', 'tmp.sol'])
    if r == 10:
        print("satisfiable")
    elif r == 20:
        print("unsat")
        r = call(['./cryptominisat5', 'tmp.cnf'], stdout=logFile)
        if r == 20:
            print("checked")
        else:
            raise "INVALID UNSAT"
    else:
        raise "INVALID RETURN VALUE"
