"""A Sage notebook can issue consecutive exploration requests without replacing its caches."""
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch

from gkm_report_cli import explore_report


class NativeExploration(unittest.TestCase):
    def test_consecutive_requests_and_failed_worker_leave_the_caller_intact(self):
        roots = []
        keys = ("DOT_SAGE", "ADMCYCLES_CACHE_DIR", "MPLCONFIGDIR", "XDG_CACHE_HOME")
        caller = {key: os.environ.get(key) for key in keys}
        requests = {"X0": [((1,), (1,), ("pt",))], "X1": [], "X2": []}

        def worker(command, *, env, check):
            self.assertEqual(command[0], sys.executable)
            self.assertTrue(check)
            paths = [Path(env[key]) for key in keys]
            self.assertTrue(all(p.is_dir() for p in paths))
            self.assertTrue((paths[0] / "admcycles").is_dir())
            self.assertEqual(caller, {key: os.environ.get(key) for key in keys})
            roots.append(paths[0].parent)
            supplied = json.loads(Path(command[-2]).read_text())
            self.assertEqual(supplied["requests"]["X0"], [[[1], [1], ["pt"]]])
            if supplied["kind"] == "failure":
                raise subprocess.CalledProcessError(1, command)
            Path(command[-1]).write_bytes(b"complete")

        with patch("gkm_report_cli.subprocess.run", side_effect=worker):
            for _ in range(2):
                self.assertEqual(explore_report(Path.cwd(), requests, 0, "plane"), b"complete")
            with self.assertRaises(subprocess.CalledProcessError):
                explore_report(Path.cwd(), requests, 0, "failure")
        self.assertEqual(len(set(roots)), 3)
        self.assertFalse(any(p.exists() for p in roots))
        self.assertEqual(caller, {key: os.environ.get(key) for key in keys})
