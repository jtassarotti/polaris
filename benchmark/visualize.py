#!/usr/bin/env python3
import argparse, sys, pprint, itertools
import matplotlib.pyplot as plt
import parse_log

markers = itertools.cycle([(3, 0), (3, 0, 180), (4, 0), (4, 0, 45), (8, 0)])

# read command-line arguments
parser = argparse.ArgumentParser(description='Visualize iris-coq build times')
parser.add_argument("-f", "--file",
                    dest="file", required=True,
                    help="Filename to get the data from.")
parser.add_argument("-t", "--timings", nargs='+',
                    dest="timings",
                    help="The names of the Coq files (with or without the extension) whose timings should be extracted")
parser.add_argument("-c", "--commits",
                    dest="commits",
                    help="Restrict the graph to the given commits.")
args = parser.parse_args()
pp = pprint.PrettyPrinter()
log_file = sys.stdin if args.file == "-" else open(args.file, "r")

results = parse_log.parse(log_file, parse_times = parse_log.PARSE_FULL)
if args.commits:
    commits = set(parse_log.parse_git_commits(args.commits))
    results = filter(lambda r: r.commit in commits, results)
results = list(results)

timings = list(map(lambda t: t[:-2] if t.endswith(".v") else t, args.timings))
for timing in timings:
    plt.plot(list(map(lambda r: r.times.get(timing), results)), marker=next(markers), markersize=8)
plt.legend(timings, loc = 'upper left', bbox_to_anchor=(1.05, 1.0))
plt.xticks(range(len(results)), list(map(lambda r: r.commit[:7], results)), rotation=70)
plt.subplots_adjust(bottom=0.2, right=0.7) # more space for the commit labels and legend

plt.xlabel('Commit')
plt.ylabel('Time (s)')
plt.title('Time to compile files')
plt.grid(True)
plt.show()
