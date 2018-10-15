import re, subprocess

class Result:
    def __init__(self, commit, times):
        self.commit = commit
        self.times = times

PARSE_NOT  = 0
PARSE_RAW  = 1
PARSE_FULL = 2

def parse(file, parse_times = PARSE_FULL):
    '''[file] should be a file-like object, an iterator over the lines.
       yields a list of Result objects.'''
    commit_re = re.compile("^# ([a-z0-9]+)$")
    time_re = re.compile("^([a-zA-Z0-9_/-]+) \((real|user): ([0-9.]+).* mem: ([0-9]+) ko\)$")
    commit = None
    times = None
    for line in file:
        # next commit?
        m = commit_re.match(line)
        if m is not None:
            # previous commit, if any, is done now
            if commit is not None:
                yield Result(commit, times)
            # start recording next commit
            commit = m.group(1)
            if parse_times != PARSE_NOT:
                times = [] if parse_times == PARSE_RAW else {} # reset the recorded times
            continue
        # next file time?
        m = time_re.match(line)
        if m is not None:
            if times is not None:
                if parse_times == PARSE_RAW:
                    times.append(line)
                else:
                    name = m.group(1)
                    time = float(m.group(2))
                    times[name] = time
            continue
        # nothing else we know about, ignore
    # end of file. previous commit, if any, is done now.
    if commit is not None:
        yield Result(commit, times)

def parse_git_commits(commits):
    '''Returns an iterable of SHA1s'''
    if commits.find('..') >= 0:
        # a range of commits
        commits = subprocess.check_output(["git", "rev-list", commits])
    else:
        # a single commit
        commits = subprocess.check_output(["git", "rev-parse", commits])
    output = commits.decode("utf-8").strip()
    if not output: # empty output
        return []
    return reversed(output.split('\n'))
