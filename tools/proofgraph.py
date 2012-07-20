
from lxml import etree

import argparse
import sys

# Usage: proofgraph.py [<graph_id>]
parser = argparse.ArgumentParser( description="Inference visualization script for Henry-N700." )
parser.add_argument( "--graph", help="ID of the graph that you want to visualize.", nargs=1 )
parser.add_argument( "--potential", help="Show all the path including potentials.", action="store_true", default=False )
parser.add_argument( "--input", help="The input file to be evaluated.", type=file, nargs=1, default=sys.stdin )

pa = parser.parse_args()

t			= etree.parse( pa.input )
n_lfc = 0
query = "/henry-output/result-inference/proofgraph"

if None != pa.graph:
	query = "/henry-output/learn-process/training/*/proofgraph[@id=\"%s\"]" % pa.graph

for pg in t.xpath( query ):	

	print "digraph {"

	obs_nodes = []
	other_nodes = []
	is_explained = {}

	for lit in pg.xpath( "./literal" ):

		if not pa.potential and "yes" != lit.attrib["active"]: continue
		
		nstr = "n%s [shape=\"none\", label=\"%s\", fontcolor=\"%s\"]" % (
			lit.attrib["id"], lit.text,
			"#000000" if "yes" == lit.attrib["active"] else "#cccccc" )
			
		if "2" == lit.attrib[ "type" ]: obs_nodes += [nstr]
		if "3" == lit.attrib[ "type" ]: other_nodes += [nstr]
		if "4" == lit.attrib[ "type" ]: obs_nodes += [nstr]
		
	for expl in pg.xpath( "./explanation" ):
		lhs, rhs	 = expl.text.split( "=>" )
		lhs, rhs	 = lhs.split( "^" ), rhs.split( "^" )
		line_style = "solid" if "yes" == expl.attrib["active"] else "dotted"

		if not pa.potential and "yes" != expl.attrib["active"]: continue
		
		for explainee in rhs:
			explainee = explainee.strip()
			is_explained[ explainee ] = 1
			
			if len( lhs ) > 1:
				n_lfc += 1
				print "lfc%d [label=\"^\", style=\"%s\"]" % (n_lfc, line_style)
				print "lfc%d -> n%s [style=\"%s\"]" % (n_lfc, explainee, line_style)
			
			for explainer in lhs:
				explainer = explainer.strip()
				if len( lhs ) > 1:
					print "n%s -> lfc%d [style=\"%s\"]" % (explainer, n_lfc, line_style)
				else:
					print "n%s -> n%s [style=\"%s\"]" % (explainer, explainee, line_style)

	u_log = {}
	
	for unif in pg.xpath( "./unification" ):
		if u_log.has_key( unif.attrib["l1"] + unif.attrib["l2"] ) or u_log.has_key( unif.attrib["l2"] + unif.attrib["l1"] ): continue
		u_log[ unif.attrib["l1"] + unif.attrib["l2"] ] = 1

		if not pa.potential and "yes" != unif.attrib["active"]: continue
		
		print "n%s -> n%s [dir=\"none\", label=\"%s\", style=\"dotted\", fontcolor=\"%s\" color=\"%s\"]" % (
			unif.attrib["l1"], unif.attrib["l2"], unif.attrib["unifier"],
			"#000000" if "yes" == unif.attrib["active"] else "#999999", "#bb0000" if "yes" == unif.attrib["active"] else "#bb6666")
					
	def coloring( nodes ):
		return [n if is_explained.has_key( n.split( " " )[0][1:] ) else n.replace( "#000000", "#bb0000" ) for n in nodes]
	
	print "subgraph cluster_o {"
	print "\n".join( coloring( obs_nodes ) )
	print "}"

	print "\n".join( coloring( other_nodes ) )
	
	print "}"
