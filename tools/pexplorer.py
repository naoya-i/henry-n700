
import sys

import re
import argparse
import collections

xml_tag_t = collections.namedtuple("xml_tag_t", "text attrib")

def parseTag(ln):
	try:
		return xml_tag_t(re.findall(">(.*?)<\/", ln)[0], dict(re.findall("([a-z0-9]+)=\"(.*?)\"", ln)))
	except IndexError:
		return xml_tag_t("", dict(re.findall("([a-z0-9]+)=\"(.*?)\"", ln)))
	
def main():
	parser = argparse.ArgumentParser( description="Proof graph explorer for Henry-N700." )
	parser.add_argument("--input", help="", type=file, default=sys.stdin)

	pa	 = parser.parse_args()
	itch = False

	nodesObs = []
	literals = {}
	edges		 = collections.defaultdict(list)
	unifs		 = collections.defaultdict(list)
	
	for ln in pa.input:
		ln = ln.strip()
		
		if "<proofgraph" in ln: itch = True
		if "</proofgraph" in ln: break
		
		if itch and "<literal" in ln:
			# Example: <literal id="1749" type="3" depth="0" active="no">=(_26,_12):1749:0.00</literal>
			t = parseTag(ln)
			literals[t.attrib["id"]] = t

			if "2" == t.attrib["type"]: nodesObs += [t.attrib["id"]]

		if itch and "<explanation" in ln:
			# <explanation name="personStopsCarML" active="yes" axiom="">19 ^ 20 ^ 21 => 6</explanation>
			t = parseTag(ln)
			eStart, eEnd = t.text.split(" => ")
			edges[eEnd] += [(t, tuple(eStart.split(" ^ ")))]

		if itch and "<unification" in ln:
			# <unification l1="88" l2="20" unifier="_0=_22" active="no" />
			t = parseTag(ln)
			unifs[t.attrib["l1"]] += [(t.attrib["l2"], t.attrib["unifier"])]
			unifs[t.attrib["l2"]] += [(t.attrib["l1"], t.attrib["unifier"])]
			
	tree = []

	def _writeTree(_out, _i):
		_out += ["<li id=\"n%s\"><a id=\"an%s\">%s</a>" % (
				_i, _i,
				literals[_i].text,
				)
				]
		
		_out += ["<ul><li>Unifiables (%d)<ul>" % len(unifs[_i])]

		for j in unifs[_i]:
			_out += ["<li onClick=\"$('#jstree').jstree(true).select_node('n%(id)s'); location.href='#an%(id)s'; document.getElementById('an%(id)s').style.color='red'; document.getElementById(bf).style.color='black'; bf='an%(id)s';\">{%(eqs)s} %(label)s</li>" % {
					"id": j[0], "label": literals[j[0]].text, "eqs": j[1]}]

		_out += ["</ul></li></ul>"]

		for t, eStart in edges[_i]:
			_out += ["<ul><li><span style=\"color:red\">Assume</span> (via %s)<ul>" % t.attrib["name"]]

			for e in eStart:
				_writeTree(_out, e)

			_out += ["</ul></li></ul>"]
					
		_out += ["</li>"]
		
	for idObs in nodesObs:
		_writeTree(tree, idObs)
		
	print htmlTemplate % {
		"tree": "\n".join(tree)
		}

htmlTemplate = """<!DOCTYPE html>
<html>
  <head>
    <meta charset="utf-8">
    <title>Henry Proof Graph Explorer</title>
    <link rel="stylesheet" href="jstree-dist/themes/default/style.min.css" />
  </head>
  <body>
    <h1>Henry Proof Graph Explorer</h1>

    <input type="button" value="Collapse All" onclick="$('#jstree').jstree('close_all');" />
    <input type="button" value="Expand All" onclick="$('#jstree').jstree('open_all');" />

<input type="button" value="Find:" onclick="var ids=document.getElementById('txtFindTarget').value.split(','); for(var i=0; i<ids.length; i++) { $('#jstree').jstree(true).select_node('n'+ids[i]); }; "/>
<input type="text" id="txtFindTarget" />

    <div id="jstree">
      <ul>
      %(tree)s
      </ul>
    </div>
    
    <script src="jstree-dist/libs/jquery.js"></script>
    <script src="jstree-dist/jstree.min.js"></script>
    <script>
      var bf = '';

      $(function () {
        $('#jstree')
        .on('changed.jstree', function(e, data) {
          //
        })
        .jstree();
      });
    </script>
  </body>
</html>"""

if "__main__" == __name__: main()
