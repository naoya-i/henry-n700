#
# HENRY EXTERNAL MODULE FOR HOBBS ET AL. (93)'S WEIGHTED ABDUCTION
#

import argparse
import sys, re, os, math, random

import henryext

from collections import defaultdict

print >>sys.stderr, "Welcome to Henry external module for Hobbs et al. (93)!"

parser = argparse.ArgumentParser("Henry external module for Hobbs et al. (93)")
parser.add_argument("--minimal", help="Use minimal heuristics as an intial weight vector.", action="store_true")
parser.add_argument("--random", help="Use random values as an intial weight vector.", action="store_true")
parser.add_argument("--disjoint", help="Use disjoint axiom feature (w/fixed infinite weight).", action="store_true")
parser.add_argument("--disjointfeature", help="Use disjoint axiom feature.", action="store_true")
parser.add_argument("--genaxiom", help="Use generalized axiom feature.", action="store_true")
if "argv" in dir(sys): parser.print_help(); sys.exit()

g_disj  = dict( [(x.strip(), None) for x in open( "/home/naoya-i/work/unkconf2012/plan-disj.tsv" ) ] )

pa = parser.parse_args(sys.argv[1:] if "argv" in dir(sys) else _args.split())

plan_predicates = """inst_smarket_shopping shopper thing_shopped_for store inst_liqst_shopping inst_shopping
inst_robbing robber place_rob victim_rob weapon_rob thing_robbed
inst_going_by_plane goer plane_luggage source_go plane_ticket vehicle
inst_going_by_bus dest_go bus_driver token
inst_rest_dining diner restaurant rest_thing_ordered rest_thing_drunk rest_drink_straw
inst_drinking drinker patient_drink instr_drink
inst_going_by_taxi taxi_driver
inst_paying payer thing_paid
inst_jogging jogger jog_thing_drunk jog_drink_straw
inst_partying agent_party party_thing_drunk party_drink_straw""".split()

#
def cbInitializeWeight(ctx, name):
	if pa.random: return -1.0 + random.random()*2
	
	if pa.minimal:
		if "UNIF" in name: return 1.0
		if "HYPOTHESIZED" in name: return -1.0
		if "EXPLAINED" in name: return 1.0

	if "UNIF" in name: return 0.1
	
	return -0.0001

#
# CALLBACK: SCORE FUNCTION
#
def cbScoreFunction( ctx ):

	ret		= []
	set_p = henryext.getLiterals( ctx )

	for p in set_p:
		if henryext.isTimeout(ctx): return ret
		if "=" == p[0]: continue

		if 1 == p[8]:
			ret += [([["p%d" % p[2]]], "$PROHIBITED_%s" % (p[0]), -10000)]

		else:
			# COST FOR p.
			if 4 == p[6]:
				ret += [([["p%d" % p[2]]], "$HYPOTHESIZED_%s" % (p[0]), -10000)] #-p[5]-0.001)]

			else:
				ret += [([["p%d" % p[2]]], "HYPOTHESIZED_%s_%s" % (p[0], p[3]), 1)] #-p[5]-0.001)]
				#ret += [([["p%d" % p[2]]], "!HYPOTHESIZED_%s" % (p[0]), -p[5]-0.001)]

		if "!=" == p[0]: continue
		
		# CREATE EXPLANATION FACTORS FOR p.
		dnf_expl, expl = [], defaultdict(list)

		for q in set_p:
			if q[0] in ["=", "!="]: continue
			if p[2] == q[2]:        continue
			if 4 == q[6]:           continue

			if "" != p[4] and "" != q[4]:

				# SELF-EXPLANATION IS PROHIBITED. (p => q => p)
				if repr(q[2]) in p[4].split(","): continue
				
			fc_cooc				 = ["p%d" % p[2], "p%d" % q[2]]
			fc_cooc_vuall  = fc_cooc + (["c%s %s" % (p[1][i], q[1][i]) for i in xrange(len(p[1]))] if len(p[1]) == len(q[1]) else [])
			
			# if (2 == p[6] and 3 == q[6]) or (2 == q[6] and 3 == p[6]):
			# 	ret += [([fc_cooc], "COOC_%s-%s" % (max(p[0],q[0]), min(p[0],q[0])), 1)]

			# if 3 == p[6] and 3 == q[6]:
			# 	ret += [([fc_cooc], "HYPO_COOC_%s-%s" % (max(p[0],q[0]), min(p[0],q[0])), 1)]

			# if p[0] != q[0] and (("inst_" in p[0] and "inst_" not in q[0]) or ("inst_" in q[0] and "inst_" not in p[0])) and p[0] in plan_predicates and q[0] in plan_predicates:
			# 	ret +=  [([fc_cooc], "HYPO_PLANPREDS_%s-%s" % (max(p[0],q[0]), min(p[0],q[0])), 1)]
			
			#
			# EXPLANATION FOR p.
			if 4 != p[6]:
				if p[0] != q[0] and repr(p[2]) in q[4].split(","): expl[(q[7], q[3])] += ["p%d" % q[2]]
				
			#
			# EXPLANATION BY UNIFICATION.
			# if "" != p[4] and "" != q[4]:

			# 	# IF THEY ARE EXPLAINING THE SAME THING, JUST IGNORE THEM. (p => q, p => q)
			# 	if 0 < len(set(p[4].split(",")) & set(q[4].split(","))): continue

			if g_disj.has_key("%s/1\t%s/1" % (p[0], q[0])) or g_disj.has_key("%s/1\t%s/1" % (q[0], p[0])):
				if pa.disjoint:
					ret += [([fc_cooc_vuall], "DISJOINT_%s-%s" % (max(p[0],q[0]), min(p[0],q[0])), -9999)]
				elif pa.disjointfeature:
					ret += [([fc_cooc_vuall], "DISJOINT_%s-%s" % (max(p[0],q[0]), min(p[0],q[0])), 1)]
					
			#
			# BELOW ARE EXPLANATION BY UNIFICATION; AVOID DOUBLE-COUNT.			
			_bothStartsWith = lambda x: p[0].startswith(x) and q[0].startswith(x)
			_samePreds      = lambda: p[0] == q[0]

			# CLASSICAL UNIFICATION.
			if _samePreds():
				if 4 == p[6]:
					dnf_expl += [fc_cooc_vuall]
					
				elif (p[5] > q[5] or (p[5] == q[5] and p[2] > q[2])):
					dnf_expl += [fc_cooc_vuall]
					ret += [([fc_cooc_vuall], "UNIFY_%s" % p[0], 1)]

		# CREATE FEATURE FOR THE DNF.
		if 4 == p[6]:
			ret += [(dnf_expl, "$EXPLAINED_BY_UNIF_%s" % (p[0]), 10000)]

		else:
			# ret += [(dnf_expl, "!EXPLAINED_BY_UNIF_%s" % (p[0]), 1)] #p[5])]
			#ret += [(expl.values(), "EXPLAINED_BY_LIT_%s" % (p[0]), 1)] #p[5])]
			# ret += [(dnf_expl+expl.values(), "!EXPLAINED_BY_LIT_%s" % (p[0]), p[5])]
			ret += [(dnf_expl+expl.values(), "EXPLAINED_BY_%s_%s" % (p[0], p[3]), 1)]
			
			for k, v in expl.iteritems():
				# ret += [([v], "AXIOM_%s" % (k[1] if not pa.genaxiom else "_".join(k[1].split("_")[:-1])), 1)]
				if "" == p[10]: continue
				
			 	ret += [([v], "AXIOM_%s" % p[10], 1)]
				
	return ret

#
# CALLBACK: PREPROCESSING
#
def cbPreprocess( ctx, obs ):
	return [] # DO NOTHING.

#
# CALLBACK: LOSS FUNCTION
#
def cbGetLoss(ctx, system, gold):
	if "" == system: return (1, [])
	
	gold_not = sorted( filter( lambda x: x.startswith( "!" ), gold.split( " ^ " ) ) )
	gold_pos = sorted( filter( lambda x: not x.startswith( "!" ), gold.split( " ^ " ) ) )

	num_pos_loss, num_neg_loss = 0, 0

	for lit in gold_pos:
		lit = _break(lit)
		if lit[0] not in plan_predicates: continue
		
		positives = filter( lambda x: x.split("(")[0] == lit[0], system.split( " ^ " ) )

		if 0 == len(positives):
			num_pos_loss += 1
			print lit

	print system, gold_pos
	
	for lit in _shrink(system.split(" ^ ")):
		lit = _break(lit)
		if lit[0] not in plan_predicates: continue
		
		positives = filter( lambda x: x.split("(")[0] == lit[0], gold_pos)

		if 0 == len(positives):
			num_pos_loss += 1
			print lit
	
			
	# Loss for positive predicates.
	# for lit in gold_pos:
	# 	lit = _break(lit)

	# 	positives = filter( lambda x: x.split("(")[0] == lit[0], system.split( " ^ " ) )

	# 	if 0 == len(positives):
	# 		num_pos_loss += 1
		
	# # Loss for negative literals.
	# for lit in gold_not:
	# 	lit = _break( _break(lit)[1][0] + ")" )

	# 	negatives = filter( lambda x: x.split("(")[0] == lit[0], system.split( " ^ " ) )
			
	# 	if len(negatives) > 0:
	# 		print >>sys.stderr, "Negative literal found:", negatives

	# 	num_neg_loss += min(len(negatives), 1)
	
	slots, alignments = {}, []
	_findGoldMatch( alignments, slots, gold_pos, _shrink(system.split(" ^ ")), {} )

	print alignments
	
	print "AL:", len(alignments), num_pos_loss, num_neg_loss, slots
	#if 0 < len( alignments ) and 0 == num_neg_loss: return (0, [])
	#if 0 < len( alignments ): return (0.0, [])

	#return (1.0*((0 if 0<len(alignments) else 1)+num_pos_loss+num_neg_loss)/(len(gold_pos)+len(gold_not)+1), [])
	return (1.0*(len(slots.keys()) - len(["" != x for x in slots.values()])+num_pos_loss+num_neg_loss)/1.0, [])
	return ((0 if 0<len(alignments) else 1) + 1.0*num_neg_loss/len(gold_not), []) # DO NOTHING.

# "PRED(ARG1, ARG2, ARG3, ...)" => ("PRED", ["ARG1", "ARG2", "ARG3", ...])
def _break(lf): lf = re.match( "(.*?)\((.*?)\)", lf ); return (lf.group(1), lf.group(2).split(","))

# "PRED(ARG1, ARG2, ARG3)" + {ARG1: x, ARG2: y} => "PRED(x, y, ARG3)"
def _applySignature( lf, signature ): lf = _break(lf); return "%s(%s)" % (lf[0], ",".join( [signature.get( t, t ) for t in lf[1]] ) )

# ["a(x)", "b(y)", "=(x, y)"] => ["a(x)", "b(x)"]
def _shrink( lfs ):
	signature       = {}

	for eq in lfs:
		if not eq.startswith( "=" ): continue
		eq   = _break(eq)
		eq_c = filter( lambda v: v[0].isupper(), eq[1] )
		eq_k = filter( lambda v: "_" != v[0], eq[1] )
		rep  = eq_c[0] if 0 < len(eq_c) else eq_k[0] if 0 < len(eq_k) else eq[1][0]

		for v in eq[1]: signature[v] = rep

	return list( set([_applySignature( lf, signature ) for lf in lfs if not lf.startswith("=") and  not lf.startswith("!=")]) )   

#
def _findGoldMatch( out_alignments, out_slots, gold, lfs, bind_history, depth = 1 ):

	for i, glf_i in enumerate(gold):
		sglf = _break( glf_i )
		head = "%s %s %s:" % (("-" * depth), str(bind_history), glf_i)

		for t in sglf[1]: out_slots[t] = ""
		
		print >>sys.stderr, head

		# Search for the literal with the same predicate with glf_i.
		for lf in lfs:
			slf = _break( lf )

			if sglf[0] != slf[0]: continue

			print >>sys.stderr, head, "Matching %s..." % lf,
			
			local_term_aligner = dict(bind_history)

			for j, term_j in enumerate(sglf[1]):
				if local_term_aligner.has_key( term_j ) and slf[1][j] != local_term_aligner[ term_j ]:
					print >>sys.stderr, "oops at %s != %s" % (slf[1][j], local_term_aligner[ term_j ])
					break
				else:
					local_term_aligner[ term_j ] = slf[1][j]
					out_slots[term_j] = slf[1][j]

			else:
				if 0 < len(gold[i+1:]):
					print >>sys.stderr, "found a valid local alignment, go into deeper..."
					_findGoldMatch( out_alignments, out_slots, gold[i+1:], lfs, local_term_aligner, depth+1 )
				else:
					out_alignments += [local_term_aligner]
					print >>sys.stderr, "Congrats!"
			
		else:
			print >>sys.stderr, head, "No more matching candidates."
			return

