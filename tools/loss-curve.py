
import argparse
import sys, os, re

parser = argparse.ArgumentParser("")
parser.add_argument("--input", help="The log file (stdout).", type=file)
parser.add_argument("--test", help="The parameter given to Henry.")
parser.add_argument("--whenfinished", help="The parameter given to Henry.")

pa = parser.parse_args()

round = 0

if "WEIGHT_FILE" not in pa.test:
	print >>sys.stderr, "No place-holder WEIGHT_FILE found!"
	sys.exit()

for ln in pa.input:
	if "(model" not in ln: continue

	print >>sys.stderr, "-- Iteration", 1+round
	round += 1
	
	print >>open("lc.weights", "w"), ln.strip()
	os.system(pa.test.replace("WEIGHT_FILE", "lc.weights").replace("LOOP", str(round)) + "> lc.stdout 2> lc.stderr")
	os.system("rm lc.weights")

	losses	 = re.findall("loss=\"([0-9.e-]+)\"", open("lc.stdout").read())
	avg_loss = sum([float(x) for x in losses]) / len(losses)

	os.system(pa.whenfinished.replace("LOOP", str(round)).replace("AVGLOSS", "%.2f" % avg_loss))
	
	print round, avg_loss
	print >>sys.stderr, ", ".join(losses), len(losses)
	sys.stdout.flush()
