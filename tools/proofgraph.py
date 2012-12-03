
from lxml import etree
from collections import defaultdict

import argparse
import sys, re

n_lfc = 0

def main():
	parser = argparse.ArgumentParser( description="Inference visualization script for Henry-N700." )
	parser.add_argument( "--graph", help="ID of the graph that you want to visualize.", nargs="+" )
	parser.add_argument( "--potential", help="Show all the path including potentials.", action="store_true", default=False )
	parser.add_argument( "--path", help="Path to henry output.", default="/" )
	parser.add_argument( "--format", help="Format (dot, or html).", default="dot" )
	parser.add_argument( "--input", help="The input file to be evaluated.", nargs="+", default=["-"] )

	pa = parser.parse_args()

	global n_lfc

	print "digraph {"
	print "graph [rankdir=LR];"
	
	for f in pa.input:
		t			= etree.parse( open(f) if "-" != f else sys.stdin )
		n_lfc = 0

		for g in pa.graph:
			query = "%shenry-output/result-inference/proofgraph" % pa.path
			
			if None != g:
				query = "%shenry-output/learn-process/training/*/proofgraph[@id=\"%s\"]" % (pa.path, g)

				if 0 == len( t.xpath( query ) ):
					query = "%shenry-output/result-inference[@target=\"%s\"]/proofgraph" % (pa.path, g)

			if 0 == len(t.xpath(query)):
				print >>sys.stderr, "No proof graph found. Did you produce the input file with \"-O proofgraph\" option?"

			for pg in t.xpath(query):
				if "dot" == pa.format:    _outputDot(t, pg, pa)
				elif "html" == pa.format: _outputHtml(t, pg)

	print "}"
		

def _outputHtml(t, pg):

	explained_by = defaultdict(list)
	literals     = {}
	
	for expl in pg.xpath( "./explanation" ):
		lhs, rhs	 = expl.text.split( "=>" )
		lhs, rhs	 = lhs.split( "^" ), rhs.split( "^" )

		for p1 in lhs:
			for p2 in rhs:
				explained_by[p2.strip()] += [(expl.attrib["name"], p1.strip())]

	for lit in pg.xpath( "./literal" ):
		literals[lit.attrib["id"]] = lit

	print """<html>
<head>
<script type="text/javascript">
var g_lit_list = new Array(%s), g_locations = {}, g_target=-1;

function _initialize() {
  for(var i=0; i<g_lit_list.length; i++) {
    var obj_i = document.getElementById('lit' + g_lit_list[i]);
    if(null == obj_i) continue;
    g_locations[g_lit_list[i]] = {x: (200*i), y: 0};
  }
  setInterval('_timer()', 100);
}

function _timer() {
  velocity = {}

  for(var i=0; i<g_lit_list.length; i++) {
    var obj_i = document.getElementById('lit' + g_lit_list[i]);
    if(null == obj_i) continue;
    velocity[i] = {x: 0, y: 0};
    if(g_target == g_lit_list[i]) continue;
    for(var j=0; j<g_lit_list.length; j++) { if(i==j) continue;
      var obj_j = document.getElementById('lit' + g_lit_list[j]);
      if(null == obj_j) continue;
      var vx    = g_locations[g_lit_list[j]].x - g_locations[g_lit_list[i]].x, vy = g_locations[g_lit_list[j]].y - g_locations[g_lit_list[i]].y;
      var vnorm = Math.sqrt(vx*vx + vy*vy);
      if(0 == vnorm) continue;
      velocity[i].x += (0.01*(200-vnorm)) * -vx/vnorm;
      velocity[i].y += (0.01*(200-vnorm)) * -vy/vnorm;
    }
  }

  /* Update the positions. */
  for(var i=0; i<g_lit_list.length; i++) {
    var obj_i = document.getElementById('lit' + g_lit_list[i]);
    if(null == obj_i) continue;
    g_locations[g_lit_list[i]].x += Math.max(-1,Math.min(1,velocity[i].x));
    g_locations[g_lit_list[i]].y += Math.max(-1,Math.min(1,velocity[i].y));
    obj_i.style.left = g_locations[g_lit_list[i]].x + "px";
    obj_i.style.top  = g_locations[g_lit_list[i]].y + "px";
  }
}

var light_up_colors = {'literals': 'yellow', 'terms': '#ffcccc', 'axioms': '#ccccff'};

function _lightUp(x, type, f_reset) {
  var terms = document.getElementsByName(type);
  for(var i=0; i<terms.length; i++)
    if(-1 != terms[i].innerHTML.split("=").indexOf(x)) terms[i].style.background = light_up_colors[type];
    else if(f_reset)            terms[i].style.background =  'white';
}

function _lightUpById(x) {
  document.getElementById(x).style.background = 'yellow';
}

function _annotateFactor(x, n) {
  _lightUp('hmmmmm', 'literals', true);
  _lightUp('hmmmmm', 'terms', true);
  document.getElementById('div_status').innerHTML = 'Factor '+ n +':<br /><code>'+ x.replace(/\\n/g, "<br />") +'</code>';
	var lines=x.split("\\n");
	for(var j=0;j<lines.length;j++) {
		if(null != lines[j].match(/\):([0-9]+)$/))                _lightUpById('lit' + RegExp.$1);
		else if(null != lines[j].match(/^([^,=!]+)=([^,]+)$/) )  { _lightUp(RegExp.$1, 'terms', false); _lightUp(RegExp.$2, 'terms', false); }
		else if(null != lines[j].match(/^([^,=!]+)!=([^,]+)$/) ) { _lightUp(RegExp.$1, 'terms', false); _lightUp(RegExp.$2, 'terms', false); }
  }
}
</script>
</head>
<body>
<div style="position:fixed;bottom:0px;background-color:silver;" id="div_status">aaaaa</div>
""" % (", ".join(literals.keys()))

		# print "<span onmousedown=\"g_target=%s;\"" % lit.attrib["id"],
		# print "onmouseup=\"g_target=0;\" onmousemove=\"if(%s == g_target) g_locations[%s].x = -100+event.clientX;\"" % (lit.attrib["id"], lit.attrib["id"]),
		# print "id=\"lit%s\" style=\"position:absolute; left:0px; top:0px\">%s</span>" % (lit.attrib["id"], lit.text)

	factors			= defaultdict(list)
	factor_id		= 0
	eqv_cluster = {}
	
	for terms in re.findall("[^!]=\(([^)]+)\)", pg.xpath("../hypothesis")[0].text):
		for t in terms.split(","):
			eqv_cluster[t] = terms.replace(",", "=")
	
	for fc in pg.xpath("../score-function/factor"):
		factor_id += 1
		
		for tr in fc.attrib["name"].split("/"):
			for k in tr.split(":")[-1].split("=") if "=" in tr.split(":")[-1] else [tr.split(":")[-1]]:
				factors[k] += [(":".join([fc.attrib["name"][4:].replace("/", "\\n"), fc.attrib["value"], "ACTIVE" if 1 == float(fc.text) else "INACTIVE"]), factor_id)]
				
	for lit in pg.xpath( "./literal" ):
		if "2" != lit.attrib[ "type" ]: continue

		def _showAxiom(x):
			return "<span onclick=\"_lightUp('%s', 'axioms', true)\" name=\"axioms\" style=\"color:#000077;cursor:pointer;\" >%s</span>" % (x, x)
		
		def _showLiteral(x, id):
			x = re.findall("(.*?)\((.*?)\)", x)[0]
			
			return "%s%s(%s)" % (
				"".join(["<span onclick=\"_annotateFactor('%s', '%s');\" style=\"color:%s;cursor:pointer;\">&Phi;<sub>%s</sub></span>" % (f[0], f[1], "#ff0000" if ":ACTIVE" in f[0] else "#770000", f[1]) for f in factors.get(id, [])]),
				"<span onclick=\"_lightUp('%s', 'literals', true)\" id=\"lit%s\" name=\"literals\" style=\"cursor:pointer;\">%s</span>" % (x[0], id, x[0]),
				", ".join( ["%s<span onclick=\"_lightUp('%s', 'terms', true)\" name=\"terms\" style=\"color:#555555;background-color:white;cursor:pointer;\">%s</span>" % (
							"".join(["<span onclick=\"_annotateFactor('%s', '%s');\" style=\"color:%s;cursor:pointer;\">&Phi;<sub>%s</sub></span>" % (f[0], f[1], "#ff0000" if ":ACTIVE" in f[0] else "#770000", f[1]) for f in factors.get(y, [])]), y, eqv_cluster.get(y,y)) for y in x[1].split(",")] ) )

		print "<code style=\"white-space:nowrap;font-size:1.2em;\">"
		print "<font color=\"red\">&diams;</font> <b>%s</b><br />" % _showLiteral(lit.text, lit.attrib["id"])
		
		def _showChildren(i, depth=1):
			for ax, e_lit in sorted(explained_by[i], key=lambda x:x[1]):
				print "<font color=\"blue\">&raquo;</font> "*depth, "[%s] %s<br />" % (_showAxiom(ax), _showLiteral(literals[e_lit].text, literals[e_lit].attrib["id"]))
				_showChildren(literals[e_lit].attrib["id"], depth+1)
			
		_showChildren(lit.attrib["id"])
		print "</code>"
			
		
	print "<br /><br /><br /></body></html>"


dig_id = 0

def _outputDot(t, pg, pa):
	global dig_id
	
	print "subgraph {"
	obs_nodes = []
	other_nodes = []
	is_explained = {}

	global n_lfc

	dig_id += 1

	for lit in pg.xpath( "./literal" ):

		if not pa.potential and "yes" != lit.attrib["active"]: continue

		nstr = "n%s [shape=\"none\", label=\"%s\", fontcolor=\"%s\"]" % (
			dig_id*1000+int(lit.attrib["id"]), re.sub("!=\((.*?),(.*?)\)", r"\1 != \2", lit.text),
			("#000000" if "yes" == lit.attrib["active"] else "#cccccc") if "4" != lit.attrib[ "type" ] else "#0000cc" )

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
				print "lfc%d -> n%s [style=\"%s\"]" % (n_lfc, dig_id*1000+int(explainee), line_style)

			for explainer in lhs:
				explainer = explainer.strip()
				if len( lhs ) > 1:
					print "n%s -> lfc%d [label=\"%s\", style=\"%s\"]" % (dig_id*1000+int(explainer), n_lfc, expl.attrib["name"], line_style)
				else:
					print "n%s -> n%s [label=\"%s\", style=\"%s\"]" % (dig_id*1000+int(explainer), dig_id*1000+int(explainee), expl.attrib["name"], line_style)

	u_log = {}

	for unif in pg.xpath( "./unification" ):
		if u_log.has_key( unif.attrib["l1"] + unif.attrib["l2"] ) or u_log.has_key( unif.attrib["l2"] + unif.attrib["l1"] ): continue
		u_log[ unif.attrib["l1"] + unif.attrib["l2"] ] = 1

		if not pa.potential and "yes" != unif.attrib["active"]: continue

		print "n%s -> n%s [dir=\"none\", label=\"%s\", style=\"dotted\", fontcolor=\"%s\" color=\"%s\"]" % (
			dig_id*1000+int(unif.attrib["l1"]), dig_id*1000+int(unif.attrib["l2"]), unif.attrib["unifier"],
			"#000000" if "yes" == unif.attrib["active"] else "#999999", "#bb0000" if "yes" == unif.attrib["active"] else "#bb6666")

	def coloring( nodes ):
		return [n if is_explained.has_key( n.split( " " )[0][1:] ) else n.replace( "#000000", "#bb0000" ) for n in nodes]

	def coloringExpl( nodes, f_exp ):
		return [n if is_explained.has_key( n.split( " " )[0][1:] ) else n.replace( "#000000", "#bb0000" ) for n in nodes if f_exp == is_explained.has_key( n.split( " " )[0][1:] )]

	print "subgraph cluster_o%d {" % int(dig_id*1000)
	print "subgraph cluster_o1%d {" % int(dig_id*1000)
	print "\n".join( coloringExpl( obs_nodes, False ) ).encode('utf-8')
	print "}"

	print "subgraph cluster_o2%d {" % int(dig_id*1000)
	print "\n".join( coloringExpl( obs_nodes, True ) ).encode('utf-8')
	print "}"
	print "}"

	print "\n".join( coloringExpl( other_nodes, True ) ).encode('utf-8')
	print "\n".join( coloringExpl( other_nodes, False ) ).encode('utf-8')

	print "}"
	
if "__main__" == __name__: main()
