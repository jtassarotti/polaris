#!/usr/bin/env python3
import argparse, sys, pprint, itertools, subprocess
import requests
import parse_log

markers = itertools.cycle([(3, 0), (3, 0, 180), (4, 0), (4, 0, 45), (8, 0)])

# read command-line arguments
parser = argparse.ArgumentParser(description='Export iris-coq build times to grafana')
parser.add_argument("-f", "--file",
                    dest="file", required=True,
                    help="Filename to get the data from.")
parser.add_argument("-c", "--commits",
                    dest="commits",
                    help="Restrict the graph to the given commits.")
parser.add_argument("-p", "--project",
                    dest="project", required=True,
                    help="Project name sent to the server.")
parser.add_argument("-b", "--branch",
                    dest="branch", required=True,
                    help="Branch name sent to the server.")
parser.add_argument("-s", "--server",
                    dest="server", required=True,
                    help="The server (URL) to send the data to.")
parser.add_argument("-u", "--user",
                    dest="user", required=True,
                    help="Username for HTTP auth.")
parser.add_argument("--password",
                    dest="password", required=True,
                    help="Password for HTTP auth.")
args = parser.parse_args()
pp = pprint.PrettyPrinter()
log_file = sys.stdin if args.file == "-" else open(args.file, "r")

results = parse_log.parse(log_file, parse_times = parse_log.PARSE_RAW)
if args.commits:
    commits = set(parse_log.parse_git_commits(args.commits))
    results = filter(lambda r: r.commit in commits, results)
results = list(results)

for datapoint in results:
    times = ''.join(datapoint.times)
    commit = datapoint.commit
    date = subprocess.check_output(['git', 'show', commit, '-s', '--pretty=%cI']).strip().decode('UTF-8')
    headers = {'X-Project': args.project, 'X-Branch': args.branch, 'X-Commit': commit, 'X-Date': date}
    r = requests.post(args.server, data=times, headers=headers, auth=(args.user, args.password))
    r.raise_for_status()

