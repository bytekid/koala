import json
import re
from subprocess import check_output

if __name__ == "__main__":
  f = open("data/decidability.json", "r")
  decdata = json.loads(f.read())
  dec = dict([(s,p) for (s,p) in decdata.items() if p["error"] == ""])

  f = open("data/no_equality_no_arith.txt", "r")
  problems = f.read().split("\n")
  print(str(len(problems)) + " problems")
  problems = [p for p in problems if p in dec]
  print(str(len(problems)) + " problems not too large")

  tools = {}
  tools["koala"] = json.loads(open("data/thefixedkoalaresults.json", "r").read())
  tools["e"] = json.loads(open("data/other_tools/E.json", "r").read())
  tools["vampire"] = json.loads(open("data/other_tools/vampire.json", "r").read())
  tools["darwin"] = json.loads(open("data/other_tools/darwin.json", "r").read())
  tools["darwinfm"] = json.loads(open("data/other_tools/darwinFM.json", "r").read())
  tools["cvc5"] = json.loads(open("data/other_tools/cvc5.json", "r").read())
  tools["cvc5fm"] = json.loads(open("data/other_tools/cvc5fm.json", "r").read())
  tools["iprover"] = json.loads(open("data/other_tools/iprover.json", "r").read())

  toolnames = ["koala", "e", "vampire", "iprover", "cvc5", "cvc5fm", "darwin", "darwinfm"]

  properties = ["is_ground", "is_epr", "is_stratified", "is_monadic", "is_2var", \
    "is_ackermann", "is_guarded", "is_pvd", "is_sort_pvd", "is_restrained", \
    "is_sort_restrained"]
  pnames = {"is_ground": "ground", "is_epr": "EPR", "is_stratified": "stratified", "is_monadic":"monadic", "is_2var":"FO$^2$", \
    "is_ackermann":"Ackermann", "is_guarded":"guarded", "is_pvd":"PVD", "is_sort_pvd":"sort-refined PVD", "is_restrained":"restrained", \
    "is_sort_restrained":"sort-restrained" }
  
  print("\\begin{tabular}{c | @{\\ }r")
  for p in toolnames:
    print(" | r")
  print("}")
  print("problem & \\#") 
  for p in toolnames:
    print("& %s" % p) 
  print("\\\\[-.5ex]")
  print("class & sets")
  for p in toolnames:
    print("& ")
  print("\\\\ \hline")
  
  for prop in properties:
    ps = [p for p in problems if dec[p][prop]]
    #satcount = [p for p in ps if dec[p]["status"] in ["SAT", "CSAT"]]
    unsatcount = [p for p in ps if dec[p]["status"] in ["UNSAT", "THM"]]
    print("%s & %d" % (pnames[prop], len(unsatcount)))
    
    for t in toolnames:
      results = tools[t]
      #sat = [ p for p in ps if results[p]["result"] == "SAT"]
      unsat = [ p for p in ps if results[p]["result"] in ["UNSAT", "THM", "CSAT"]]
      print("& %d " % (len(unsat)))
    print("\\\\")
    
  # others
  ps = [p for p in problems if not any(dec[p][prop] for prop in properties)]
  print("others & %d" % (len([p for p in ps if results[p]["result"] in ["UNSAT", "THM"]])))
  for t in toolnames:
    results = tools[t]
    #sat = [ p for p in ps if results[p]["result"] == "SAT"]
    unsat = [ p for p in ps if results[p]["result"] in ["UNSAT", "THM"]]
    print("& %d " % (len(unsat)))
  print("\\\\")
    
  # all
  ps = problems
  print("all & %d" % (len([p for p in ps if results[p]["result"] in ["UNSAT", "THM"] ])))
  for t in toolnames:
    results = tools[t]
    #sat = [ p for p in ps if results[p]["result"] in ["UNSAT", "THM"]]
    unsat = [ p for p in ps if results[p]["result"] == "UNSAT"]
    print("& %d" % (len(unsat)))
  print("\\\\")

  print("\\end{tabular}")
  
  for x in [p for p in problems if dec[p]["is_ground"] and tools["koala"][p]["result"] in ["UNSAT", "THM"] and tools["vampire"][p]["result"] not in ["UNSAT", "THM"]]:
    print(x)
  #print("successes", len([p for p in problems if tools["koala"][p]["success"] == "SUC"]))
  #print("sat", len([p for p in problems if tools["koala"][p]["result"] == "SAT"]))
  #print("unsat", len([p for p in problems if tools["koala"][p]["result"] == "UNSAT"]))
  #problematic = [(p, tools["koala"][p]["result"], dec[p]["status"]) \
  #  for p in problems if tools["koala"][p]["success"] == "SUC" \
  #  and tools["koala"][p]["result"] != dec[p]["status"] \
  #  and tools["koala"][p]["result"] != "TIMEOUT" \
  #  and not (tools["koala"][p]["result"] == "UNSAT" and dec[p]["status"] == "THM") \
  #  and not (tools["koala"][p]["result"] == "SAT" and dec[p]["status"] == "CSAT")  ]
  #for (p, wrong, correct) in problematic:
  #  f = open("sggsruns/"+p+".txt", "r")
  #  out = f.read()
  #  if (correct == "UNSAT" or correct == "THM") and "Unsatisfiable" in out:
  #    print(p + " actually correct")
  #    tools["koala"][p]["result"] = "UNSAT"
  #  elif "TIMEOUT" in out:
  #    tools["koala"][p]["result"] = "TIMEOUT"
  #    tools["koala"][p]["success"] = "TMO"
  #    print(p + " actually timed out")
  #  else:
  #    print(p + " sucks")


  #f = open("data/thefixedkoalaresults.json", "w")
  #with open('data/thefixedkoalaresults.json', 'w') as f:
  #  json.dump(tools["koala"], f)
  for prop in properties:
    ps = [x for x in problems if dec[x][prop]]
    cnt = len(ps)
    sat = [p for p in ps if tools["koala"][p]["result"] == "SAT"]
    unsat = [p for p in ps if tools["koala"][p]["result"] == "UNSAT"]
    tavg = sum([tools["koala"]["time"] for p in sat + unsat ])
    print(prop, cnt, sat, unsat)
  print("decidable", len([x for x in problems if any(dec[x][p] for p in properties)]))
