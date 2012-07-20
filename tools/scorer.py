# Usage: scorer.py <result_file>

import argparse
import evaluator

import sys, re

from lxml import etree
from collections import defaultdict

def main():

	parser = argparse.ArgumentParser( description="Evaluation script for abduction." )
	parser.add_argument( "--input", help="The input file to be evaluated.", type=file, nargs=1 )
	pa = parser.parse_args()
	
	x	= etree.parse( pa.input[0] )
	
	num_total_correct		 = 0
	num_total_system_lfs = 0
	num_total_gold			 = 0

	for result in x.xpath( "/henry-output/result-inference" ):
		system, answer = result.xpath( "hypothesis" )[0], result.xpath( "task-result" )[0]

		top_plan_regex = "^(inst_shopping|inst_smarket_shopping|inst_liqst_shopping|inst_robbing|inst_drinking|inst_paying|\
inst_rest_dining|inst_going_by_bus|inst_going_by_taxi|inst_going_by_plane|inst_jogging|inst_partying)"
		pafilter			 = lambda x: None != re.match( top_plan_regex, x )
		
		def pafilterBind( bindings ): return lambda x: None != re.match( top_plan_regex + "\((%s)\)" % "|".join( bindings ), x )

		lfs	 = sorted( evaluator._shrink( system.text.split( " ^ " ) ) )
		gold = sorted( answer.attrib[ "gold-structure" ].split( " ^ " ) )

		print "-- %s --" % result.attrib[ "target" ]

		slots, alignments = {}, []
		evaluator._findGoldMatch( alignments, slots, gold, lfs, {} )

		if 0 == len(alignments):
			best_alignment = {}
			lfs_bound      = lfs
		else:
			best_alignment = max( alignments, key=lambda x: len(x.keys()) )
			lfs_bound		 = [evaluator._applySignature( lf, best_alignment ) for lf in lfs]
		
		gold				= filter( pafilter, gold )

		# What is a variable to be evaluated?
		bindings = [evaluator._break(x)[1][0].replace( "?", "\?" ) for x in gold]
		
		lfs_bound	= filter( pafilterBind(bindings), lfs_bound )
		correct_set	= set(gold)&set(lfs_bound)

		print "Gold:", " ^ ".join( gold )
		print "System:", " ^ ".join( lfs_bound )
		print "Gold ^ System:", " ^ ".join( correct_set )
		
		print "n(G ^ S) =", len( correct_set ), "n(G) =", len( gold ), "n(S) =", len( lfs_bound )
		num_total_correct += len( correct_set ); num_total_system_lfs += len( lfs_bound ); num_total_gold += len( gold )

		print "Precision:", 100.0 * len(correct_set) / len(lfs_bound)  if 0 != len(lfs_bound) else "-"
		print "Recall:   ", 100.0 * len(correct_set) / len(gold)        if 0 != len(gold) else "-"

		

	print "-- Total --"
	print "Overall Precision:", 100.0 * num_total_correct / num_total_system_lfs
	print "Overall Recall:   ", 100.0 * num_total_correct / num_total_gold

if "__main__" == __name__: main()
