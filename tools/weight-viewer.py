
import sys, re
import argparse

def main():
	parser = argparse.ArgumentParser( description="Weight viewer." )
	parser.add_argument("--input", help="The input file to be evaluated.", nargs="+", default=["-"])
	parser.add_argument("--sorted", help="Sort.", action="store_true")
	pa = parser.parse_args()

	for f_input in pa.input:
		f_input = open(f_input) if "-" != f_input else sys.stdin

		weights = re.findall("\(weight \"(.*?)\" ([-e0-9.+]+)\)", f_input.read())
		max_len = max([len(f) for f,w in weights])
		
		for f, w in sorted(weights, key=lambda x: float(x[1]), reverse=True) if pa.sorted else weights:
			try:
				print f.ljust(max_len), "%f" % float(w)

			except IOError:
				break
			
		
if "__main__" == __name__: main()
