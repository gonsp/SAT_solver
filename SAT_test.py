from subprocess import call
import sys
import resource


class Result:
    def __init__(self, name, time, satisfiable):
        self.name = name
        self.time = time
        self.satisfiable = satisfiable


def main():
    results = list()
    with open("./results/goal_results.txt") as f:
        lines = f.readlines()
    lines = [line.strip() for line in lines]
    while(lines):
        name = (lines.pop(0))
        satisfiable = lines.pop(0) == "SATISFIABLE"
        time = float(lines.pop(0))
        results.append(Result(name, time, satisfiable))

    prev_time = 0
    for result in results:
        code = call([sys.argv[1], "./inputs/" + result.name])
        act_time = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime
        if code != 10 and code != 20:
            print(result.name, "ERROR")
        else:
            if result.satisfiable == (code == 20):
                print(result.name, "OK", end=" ----- ")
                time = act_time - prev_time
                if result.time < time:
                    print("OUT OF TIME:", result.time, "->", round(act_time - prev_time, 2))
                else:
                    print("IN TIME!")
            else:
                print(result.name, "INCORRECT")
        prev_time = act_time


if __name__ == "__main__":
    main()
