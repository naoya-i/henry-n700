#
# HENRY EXTERNAL MODULE FOR HOBBS ET AL. (93)'S WEIGHTED ABDUCTION
#

import argparse
import sys, re, os, math

import henryext

from collections import defaultdict

print >>sys.stderr, "Welcome to Henry external module for Hobbs et al. (93)!"

parser = argparse.ArgumentParser("Henry external module for Hobbs et al. (93)")
if "argv" in dir(sys): parser.print_help(); sys.exit()

#
# CALLBACK: SCORE FUNCTION
#
def cbScoreFunction( ctx ):
	ret		= []
	set_p = henryext.getLiterals( ctx )

	for p in set_p:
		if henryext.isTimeout(ctx): return ret
		if "=" == p[0]: continue

		# COST FOR p.
		ret += [([["p%d" % p[2]]], "!HYPOTHESIZED_%s_%s" % (p[0], p[2]), -p[5]-0.001)]

		if "!=" == p[0]: continue
		
		# CREATE EXPLANATION FACTORS FOR p.
		dnf_expl, expl = [], defaultdict(list)

		for q in set_p:
			if q[0] in ["=", "!="]: continue
			if p[2] == q[2]:        continue

			fc_cooc				 = ["p%d" % p[2], "p%d" % q[2]]
			fc_cooc_vuall  = fc_cooc + (["c%s %s" % (p[1][i], q[1][i]) for i in xrange(len(p[1]))] if len(p[1]) == len(q[1]) else [])
			
			#
			# EXPLANATION FOR p.
			if repr(p[2]) in q[4].split(","):
				
				# SELF-EXPLANATION IS PROHIBITED. (p => q => p)
				if repr(q[2]) in p[4].split(","): continue

				expl[q[7]] += ["p%d" % q[2]]

				
			#
			# EXPLANATION BY UNIFICATION.
			if "" != p[4] and "" != q[4]:

				# IF THEY HAVE EXPLAINER-EXPLAINEE RELATIONS SHIPS, DO NOT UNIFY THEM. (p => ... => q)
				if repr(q[2]) in p[4].split(","): continue
				if repr(p[2]) in q[4].split(","): continue
				#if 0 < len(set(p[4].split(",")) & set(q[4].split(","))): continue

			#
			# BELOW ARE EXPLANATION BY UNIFICATION; AVOID DOUBLE-COUNT.			
			_bothStartsWith = lambda x: p[0].startswith(x) and q[0].startswith(x)
			_samePreds      = lambda: p[0] == q[0]

			# CLASSICAL UNIFICATION.
			if _samePreds() and (p[5] > q[5] or (p[5] == q[5] and p[2] > q[2])):
				for i in xrange(len(p[1])):
					if p[1][i] != q[1][i] and p[1][i][0].isupper() and q[1][i][0].isupper(): break
				else:
					dnf_expl += [fc_cooc_vuall]

		# GROUPING BY THE CONJUNCTIONS.
		dnf_expl += expl.values()
		
		# CREATE FEATURE FOR THE DNF.
		ret += [(dnf_expl, "!EXPLAINED_%s_%s" % (p[0], p[2]), p[5])]
			
	return ret

#
# CALLBACK: PREPROCESSING
#
def cbPreprocess( ctx, obs ):
	return [] # DO NOTHING.

#
# CALLBACK: LOSS FUNCTION
#
def cbGetLoss( ctx, system, gold ):
	return (0.0, []) # DO NOTHING.

