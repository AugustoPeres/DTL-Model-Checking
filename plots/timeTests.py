import subprocess
import timeit
import functools
import numpy as np


def send_mc_command_classical(formula, trfile):
    aux = lambda x: subprocess.check_output(x, shell = True)
    niterations = 3
    timeoutvalue = 180
    command = "gtimeout " + str(timeoutvalue) + " dtl-model-checking-exe -modelCheck {i} \"{j}\" 2".format(j=formula, i=trfile)
    try:
        time = timeit.timeit(
                   functools.partial(aux, command),
                   number = niterations
       )
        return time/niterations
    except Exception as e:
        print(e)
        return timeoutvalue #this corresponds to the timeout value

def get_times_classical_approach(formulas, systems):
    values = np.zeros((len(formulas), len(systems)))
    for fList in zip(formulas, range(len(formulas))):
        for tList in zip(systems, range(len(systems))):
            times = []
            for f in fList[0]:
                for t in tList[0]:
                    times.append(send_mc_command_classical(f, t))
            values [fList[1], tList[1]] = sum(times) / len(times)
    return values

# create an aux function that keeps track of the time outs that occur
# we should also filter out any times equal to the timeout value from the
# computation of the mean value


if __name__ == '__main__':
    formulasWithLength2 = ["@_1((p1)=>(p2))", "@_1(c_2(q1))", "@_1(X(p1))", "@_1(G(p1))"]
    formulasWithLength3 = ["@_1((X(p1))=>(p2))", "@_1((c_2(q1))=>(p1))", "@_1(c_2(G(q1)))", "(@_1(p1))=>(@_2(q1))"]
    formulasWithLength4 = ["@_1((c_2(q1))=>(~(p1)))", "@_1((c_2(q1))=>(X(p1)))", "(@_1(p1))=>(@_2(~(q1)))", "@_1(c_2(~(G(q1))))"]

    # Reverse this to have smaller formulas on bottom
    allFormulas = [formulasWithLength2, formulasWithLength3, formulasWithLength4]


    pathsSize8 = ["../dtl-model-checking/ExampleFiles/t8States1",
                  "../dtl-model-checking/ExampleFiles/t8States2",
                  "../dtl-model-checking/ExampleFiles/t8States3",
                  "../dtl-model-checking/ExampleFiles/t8States4"]

    pathsSize16 = ["../dtl-model-checking/ExampleFiles/t16States1",
                   "../dtl-model-checking/ExampleFiles/t16States2",
                   "../dtl-model-checking/ExampleFiles/t16States3",
                   "../dtl-model-checking/ExampleFiles/t16States4"]

    pathsSize32 = ["../dtl-model-checking/ExampleFiles/t32States1",
                  "../dtl-model-checking/ExampleFiles/t32States2",
                  "../dtl-model-checking/ExampleFiles/t32States3",
                  "../dtl-model-checking/ExampleFiles/t32States4"]

    pathsSize64 = ["../dtl-model-checking/ExampleFiles/t64States1",
                   "../dtl-model-checking/ExampleFiles/t64States2"]


    allDTSs = [pathsSize8, pathsSize16, pathsSize32, pathsSize64]

    print(get_times_classical_approach(allFormulas, allDTSs))
    # Script to make the plots
    sizeOfFormulas = ['2', '3', '4']
    sizeOfTransitionSystems = ['8', '16', '32', '126']
