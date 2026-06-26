r"""
Local plasTeX package: a fourth dependency-graph status, "deliberately abstract".

leanblueprint has only three styled states (\leanok = green, \notready = orange,
\mathlibok = dark green). This package adds a \abstractnode macro that renders a
node GREY + DASHED in the dependency graph, visually distinct from the orange
\notready (buildable) foundations.

It is used for the TQFT-style parametric wrappers -- a field theory is a functor
over an ARBITRARY cobordism geometry -- which are deliberately never instantiated
(see docs/blueprint_roadmap_plan.md, locked decision 7.1). They are NOT a TODO, so
they must not read as the orange "to build" queue.

Mechanism: plastexdepgraph drives node styling through three functions stored in
document.userdata['dep_graph'] (colorizer = border, fillcolorizer = fill,
stylerizer = graphviz style). leanblueprint sets the first two at package-load
time. This package loads AFTER blueprint (see web.tex \usepackage order), captures
those functions, and wraps them so that nodes carrying the 'abstract' flag get a
grey border, grey fill, and a dashed style; every other node delegates unchanged.
"""
from plasTeX import Command

# Grey, chosen to be unmistakably distinct from the orange \notready (#FFAA33),
# the greens (#9CEC8B/#1CAC78/#B0ECA3) and the blues (#A3D6FF).
GREY_BORDER = '#8A8A8A'
GREY_FILL = '#ECECEC'


class abstractnode(Command):
    r"""\abstractnode : mark the enclosing statement as a deliberately-abstract node."""

    def digest(self, tokens):
        Command.digest(self, tokens)
        # 'abstract' drives the grey/dashed styling below; 'notready' keeps the
        # node out of the leanok-only computations (it is not a built object), so
        # descendants resting on it are never marked fully-proved.
        self.parentNode.userdata['abstract'] = True
        self.parentNode.userdata['notready'] = True


def ProcessOptions(options, document):
    """Called when \\usepackage{abstractstatus} is processed (after blueprint)."""
    dep = document.userdata.setdefault('dep_graph', {})
    base_color = dep.get('colorizer', lambda n: '')
    base_fill = dep.get('fillcolorizer', lambda n: '')

    def colorizer(node):
        if node.userdata.get('abstract'):
            return GREY_BORDER
        return base_color(node)

    def fillcolorizer(node):
        if node.userdata.get('abstract'):
            return GREY_FILL
        return base_fill(node)

    def stylerizer(node):
        if node.userdata.get('abstract'):
            return 'filled,dashed'
        # Reproduce plastexdepgraph's default: 'filled' when there is a fill.
        return 'filled' if base_fill(node) else ''

    dep['colorizer'] = colorizer
    dep['fillcolorizer'] = fillcolorizer
    dep['stylerizer'] = stylerizer

    def add_legend():
        legend = dep.get('legend')
        if legend is not None:
            legend.append((
                'Grey dashed',
                'a <em>deliberately abstract</em> foundation: a parametric assumption '
                '(a field theory over an arbitrary cobordism geometry, and its tangent / '
                'dual / gh plumbing) that is never instantiated by design -- not a TODO'))

    document.addPostParseCallbacks(160, add_legend)
