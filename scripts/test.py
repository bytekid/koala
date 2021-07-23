import os, subprocess, multiprocessing, sys
import time
from os import listdir
from os.path import isfile, join
import re
import sys
import json

def get_problem_features():
  f = open("data/features.json", "r")
  return json.loads(f.read())

def get_problem_properties():
  f = open("data/properties.json", "r")
  return json.loads(f.read())

if __name__ == "__main__":
  features = get_problem_features()
  properties = get_problem_properties()

  for p in features:
    if "=" in p:
      continue # arithmetic
    if features[p]["num_equalities"] > 0:
      continue
    print(p)