# Usage: evaluator.py <result_file>

import sys, re

from lxml import etree
from collections import defaultdict


def loss( system, gold ):

	lfs	 = sorted( _shrink( system.split( " ^ " ) ) )
	gold_not = sorted( filter( lambda x: x.startswith( "!" ), gold.split( " ^ " ) ) )
	gold = sorted( filter( lambda x: not x.startswith( "!" ), gold.split( " ^ " ) ) )
	
	slots, alignments = {}, []
	_findGoldMatch( alignments, slots, gold, lfs, {} )

	if 0 < len( alignments ):
		best_alignment = max( alignments, key=lambda x: len(x.keys()) )
		lfs_bound			 = [_applySignature( lf, best_alignment ) for lf in lfs]
	else:
		best_alignment = {}
		lfs_bound			 = lfs

	correct_set	= set(gold)&set(lfs_bound)
	
	gold_predicates		 = [_break(lf)[0] for lf in gold]
	system_predicates	 = [_break(lf)[0] for lf in lfs]
	correct_predicates = []
	
	for p1 in gold_predicates:
		for p2 in system_predicates:
			if p1 == p2: correct_predicates += [p1]; break

	num_correct_args		 = 0
	num_correct_args_max = 0

	for lf in gold:
		for t in _break(lf)[1]:
			if t in best_alignment.values(): num_correct_args += 1
			num_correct_args_max += 1

	# Loss for negative literals.
	num_not_loss = 0

	for lit in gold_not:
		lit = _break( _break(lit)[1][0] + ")" )
		
		if lit[0] in system_predicates:
			num_not_loss += 1
	
	return num_not_loss + (len(slots.keys()) - len(best_alignment.keys())) + (len(gold_predicates) - len(correct_predicates))  #(len(gold) - len(correct_set))


# "PRED(ARG1, ARG2, ARG3, ...)" => ("PRED", ["ARG1", "ARG2", "ARG3", ...])
def _break(lf):	lf = re.match( "(.*?)\((.*?)\)", lf ); return (lf.group(1), lf.group(2).split(","))

# "PRED(ARG1, ARG2, ARG3)" + {ARG1: x, ARG2: y} => "PRED(x, y, ARG3)"
def _applySignature( lf, signature ): lf = _break(lf); return "%s(%s)" % (lf[0], ",".join( [signature.get( t, t ) for t in lf[1]] ) )

# ["a(x)", "b(y)", "=(x, y)"] => ["a(x)", "b(x)"]
def _shrink( lfs ):
	signature	= {}

	for eq in lfs:
		if not eq.startswith( "=" ): continue
		eq   = _break(eq)
		eq_c = filter( lambda v: v[0].isupper(), eq[1] )
		eq_k = filter( lambda v: "_" != v[0], eq[1] )
		rep  = eq_c[0] if 0 < len(eq_c) else eq_k[0] if 0 < len(eq_k) else eq[1][0]

		for v in eq[1]: signature[v] = rep
	
	return list( set([_applySignature( lf, signature ) for lf in lfs if not lf.startswith("=")]) )

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

			else:
				out_alignments += [local_term_aligner]
				
				if 0 < len(gold[i+1:]):
					print >>sys.stderr, "found a valid local alignment, go into deeper..."
					_findGoldMatch( out_alignments, out_slots, gold[i+1:], lfs, local_term_aligner, depth+1 )
				else:
					print >>sys.stderr, "Congrats!"
			
		else:
			print >>sys.stderr, head, "No more matching candidates."
			return

