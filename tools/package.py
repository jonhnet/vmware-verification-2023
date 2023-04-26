#!/usr/bin/env python3
"""
Tool to roll up all the Dafny files in the current directory for submission to
the grader.
"""

import os
import subprocess
import sys
import glob

path = os.path.normpath(os.getcwd())
try:
    chapter = [
        segment
        for segment in path.split(os.sep)
        if "chapter" in segment or "project" in segment
    ][-1]
except IndexError:
    sys.stderr.write("Cannot determine chapter name from current path.\n")
    sys.exit(-1)
package_name = f"{chapter}.tgz"
cmd = ["tar", "-czf", package_name] + glob.glob("*.dfy")
subprocess.call(cmd)
sys.stdout.write(f"Please upload {package_name} to the submission site.\n")
