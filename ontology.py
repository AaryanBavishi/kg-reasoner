import networkx as nx
import yaml
from sympy import symbols, Eq, solve, pi
import re
import pyshacl
import rdflib


class Reasoner(object):
    def __init__(self, graph=None):
        if graph is None:
            self.graph_ = nx.DiGraph()
        else:
            self.graph_ = nx.DiGraph(graph)
        self.inheritance_tree_ = None

    def parse_yml(self, yml_path):
        "Parse YML file and generate a NetworkX DiGraph from its contents."
        with open(yml_path, 'r') as fid:
            ont_dict = yaml.safe_load(fid)

        for key, val in ont_dict.items():
            self.graph_.add_node(key, type='object')
            if val is None:
                continue
            for i, (dk, dv) in enumerate(val.items()):
                if dk == 'properties':
                    for p, qk in dv.items():
                        prop = f'{key}.{p}'
                        self.graph_.add_node(prop, type='property', kind=qk)
                        self.graph_.add_edge(key, prop, relation='has_property')
                elif dk == 'equations':
                    for j, eq in enumerate(dv):
                        eq_key = f'{key}.Eq{j}'
                        self.graph_.add_node(eq_key, type='equation', value=eq)
                        self.graph_.add_edge(key, eq_key, relation='has_equation')
                else:
                    self.graph_.add_edge(key, dv, relation=dk)

    def fill_equation_edges(self):
        "Add edges to the graph from equation values."
        obj_nodes = [n for n, d in self.graph_.nodes(data=True) if d['type'] == 'object']
        for obj in obj_nodes:
            props = [p for p in nx.neighbors(self.graph_, obj) if self.graph_.edges[(obj, p)]['relation'] == 'has_property']
            for n, d in self.graph_.nodes(data=True):
                if d['type'] != 'equation':
                    continue
                in_formula = [it.split('.')[-1] in d['value'] for it in props]
                connected_props = [it for i, it in enumerate(props) if in_formula[i]]
                for p in connected_props:
                    self.graph_.add_edge(p, n, relation='in_equation')
                    self.graph_.add_edge(n, p, relation='from_equation')

    def get_props(self, obj):
        props = [p for p in nx.neighbors(self.graph_, obj) if 'relation' in self.graph_.edges[(obj, p)] and self.graph_.edges[(obj, p)]['relation'] == 'has_property']
        return props

    def get_eqns(self, obj):
        eqns = [p for p in nx.neighbors(self.graph_, obj) if self.graph_.nodes[p]['type'] == 'equation']
        return eqns

    def generate_inheritance_tree(self):
        "Populate a tree describing class inheritance"
        self.inheritance_tree_ = nx.DiGraph([(u, v) for u, v, e in self.graph_.edges(data=True) if e['relation'] == 'derivedFrom'])

    def find_prototypes(self):
        # return family_tree
        raise NotImplementedError

    def propagate_inheritance(self):
        "Fill inherited properties in the derived classes"
        self.generate_inheritance_tree()
        obj_nodes = [n for n, d in self.graph_.nodes(data=True) if d['type'] == 'object']
        for obj_to_fill in obj_nodes:
            path = nx.shortest_path(self.inheritance_tree_, obj_to_fill, 'Object')
            for obj in path[::-1]:  # traverse top-down so inherited properties can be overwritten
                if obj == obj_to_fill:
                    continue
                for p in self.get_props(obj):
                    # print(obj, p, '->', p.replace(obj, obj_to_fill))
                    print(f'adding property {p} to node {obj_to_fill} as {p.replace(obj, obj_to_fill)}')
                    self.graph_.add_node(p.replace(obj, obj_to_fill), **self.graph_.nodes[p])
                    self.graph_.add_edge(obj_to_fill, p.replace(obj, obj_to_fill), relation='has_property')
                for f, d in nx.ego_graph(self.graph_, obj).nodes(data=True):
                    if obj_to_fill in f:
                        continue
                    if d['type'] == 'equation':
                        n_equations = len(self.get_eqns(obj_to_fill))
                        name = f'{obj_to_fill}.Eq{n_equations}'
                        value = d['value'].replace(obj, obj_to_fill)
                        print(f"from {f}, {obj_to_fill} inheriting {value} as {name}")
                        print('> ', path)
                        self.graph_.add_node(name, type='equation', value=value)
                        self.graph_.add_edge(obj_to_fill, name, relation='has_equation')
                        # ont.add_edge(obj_to_fill, f, relation='has_equation')
                        # what if the new equation overwrites the inherited one?
                        # TODO: handle a way to suppress incorrect equations from generic classes
        self.fill_equation_edges()  # replaces the following lines (in theory)

    def fill(self, instance):
        "Fill all possible missing values from an object instance"
        # map the object onto the class from the ontology
        obj = {}
        for k, v in instance.items():
            if k == 'type':
                obj[k] = v
                continue
            key = f"{obj['type']}.{k}"
            if key not in self.graph_:
                raise ValueError(f"{key} not present in ontology")
            else:
                obj[key] = v

        print(obj)

        sub_ont = nx.ego_graph(self.graph_, obj['type'])

        props = [p for p in nx.neighbors(sub_ont, obj['type']) if
                 sub_ont.edges[(obj['type'], p)]['relation'] == 'has_property']
        s = symbols(' '.join(props))
        sym_map = {p: s[i] for i, p in enumerate(props)}

        known = [p for p in props if p in obj]
        unknown = [p for p in props if p not in known]
        print('known props:', known)
        print('unknown props:', unknown, '\n')

        # back-fill with information available
        verbose = False
        for target in unknown:
            if verbose:
                print(f'> looking for {target}')
            known = [p for p in props if p in obj]
            unknown = [p for p in props if p not in known]
            # find the path to the known properties
            for source in known:
                if target in obj:
                    break  # skip after solving
                try:
                    path = nx.shortest_path(sub_ont, source, target)
                except:
                    print(f'Warning: no path between {source} <-> {target}')
                    continue
                hops = (len(path) - 1) // 2
                if verbose:
                    print(f'    tracing {hops} hops: {" -> ".join(path)}')
                for k in range(hops):
                    # index the hyperedge across a formula
                    edge = (path[k * 2], path[k * 2 + 1], path[k * 2 + 2])
                    node_types = [sub_ont.nodes[n]['type'] for n in edge]
                    if node_types != ['property', 'equation', 'property']:
                        raise ValueError('Expected a link between Properties via a Equation')
                    if edge[2] in obj:
                        continue  # skip after solving
                    formula = sub_ont.nodes[edge[1]]['value']
                    for i, p in enumerate(props):
                        # formula = formula.replace(p.split('.')[-1], f's[{i}]')
                        formula = re.sub(r'\b%s\b' % p.split('.')[-1], f's[{i}]', formula)
                    lhs, rhs = formula.split('=')
                    eqn = Eq(eval(lhs), eval(rhs))
                    symbol = sym_map[edge[2]]
                    sol = solve(eqn, symbol)
                    # get numerical results
                    results = [root.evalf(subs=obj) for root in sol]
                    # check validity
                    # TODO: make this more elegant using xsd logic
                    validator = ShaclValidator(sub_ont)
                    validator.validate()
                   # instanceof = sub_ont.nodes[str(symbol)]['kind']
                   # valuesof = self.graph_.nodes[instanceof]['hasvaluesof']
                   # validity = self.graph_.nodes[valuesof]['valid']
                   # is_valid = [validity(it) for it in results]
                   # result = [r for r, v in zip(results, is_valid) if v]
                   # if len(result) == 1:
                   #     if verbose:
                   #         print(f'    {edge[2]} -> {result[0]}')
                   #     obj[edge[2]] = result[0]
                   # elif len(result) > 1:
                    #    raise ValueError(f'Multiply defined value for {edge[2]}:' + str(result))

        filled_obj = {k.replace(f"{obj['type']}.", ''): v for k, v in obj.items()}
        return filled_obj

class ShaclValidator:
    def __init__(self, data):
        self.data = data
        self.shape_graph = rdflib.Graph()
        self._define_shapes()

    def validate(self):
        data_graph = rdflib.Graph()
        for value in self.data.items():
            data_graph+=DataValueTemplate(value)
             
        data_graph.parse(data=data_graph, format='turtle')        
        results = pyshacl.validate(data_graph, shacl_graph=self.shape_graph, inference='rdfs', debug=False,
                                  serialize_report_graph=False)
        conforms, v_graph, v_text = result
        result = v_graph.query(self._define_shapes)
        bad_URI = [list(it.values())[0] for it in result.bindings]
        bad_nodes = [it.toPython().split('/')[-1] for it in bad_URI]
        return bad_nodes

    def _define_shapes(self):
        self.shape_graph.parse(data="""
            prefix : <http://sites.psu.edu/reinhartgroup/mykg/>
@prefix sh: <http://www.w3.org/ns/shacl#> .
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
@prefix qudt: <http://qudt.org/schema/qudt/> .
@prefix unit: <http://qudt.org/vocab/unit/> .

:myRule a sh:NodeShape ;             # enforce a Shape on the Node with type Measurement (name <myRule> can be anything)
    sh:targetClass :Measurement ;    # this should apply to :Measurement and all its subClasses
    sh:property [
        sh:path qudt:numericValue ;  # place constraints on the numericValue of the :Measurement
        sh:nodeKind sh:Literal ;     # make sure we are evaluating a literal
        sh:or ( [ sh:datatype xsd:double ] [ sh:datatype xsd:float ] [ sh:datatype xsd:decimal ] ) ;  # enforce certain datatypes
        sh:minInclusive 0.0 ;        # enforce >=0 values
        sh:minCount 1 ;              # enforce at least 1 qudt:numericValue
        sh:maxCount 1 ;              # enforce at most 1 qudt:numericValue
    ] .
""", format='turtle')

class RDFRenderer(object):
    rdf_template_ = None

    def __init__(self):
        self.rdf_ = self.rdf_template_

    def __str__(self):
        return self.rdf_


class DataValueTemplate(RDFRenderer):
    rdf_template_ = """
:<NAME> a :<TYPE> ;
  qudt:numericValue <VALUE> ;
  qudt:unit unit:<UNIT> ;
.
"""

    def __init__(self, instances):
        super().__init__()
        required = ['name', 'type', 'value', 'unit']
        for key in required:
            if key not in instances.keys():
                raise ValueError(f'{key} not in substitutions dict')
        for key, value in instances.items():
            self.rdf_ = self.rdf_.replace(f'<{key.upper()}>', str(value))


class DataGraphTemplate(RDFRenderer):
    rdf_template_ = """
prefix : <http://sites.psu.edu/reinhartgroup/mykg/>
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix qudt: <http://qudt.org/schema/qudt/> .
@prefix unit: <http://qudt.org/vocab/unit/> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
"""

    def __init__(self, instances):
        super().__init__()
        for item in instances:
            self.rdf_ += str(DataValueTemplate(item))

    def as_graph(self):
        graph = rdflib.Graph()
        graph.parse(data=self.rdf_, format='turtle')
        return graph


class Validator(object):
    sparql_query = """
SELECT ?focus
  WHERE {
    ?id rdf:type sh:ValidationResult .
    ?id sh:focusNode ?focus .
  }
"""

    def __init__(self, ont_graph, shacl_graph):
        self.ont_graph = ont_graph
        self.shacl_graph = shacl_graph

    def run(self, data_graph):
        result = pyshacl.validate(data_graph,
                                  shacl_graph=self.shacl_graph,
                                  ont_graph=self.ont_graph,
                                  inference='rdfs', debug=False,
                                  serialize_report_graph=False)
        conforms, v_graph, v_text = result

        result = v_graph.query(self.sparql_query)
        bad_URI = [list(it.values())[0] for it in result.bindings]
        bad_nodes = [it.toPython().split('/')[-1] for it in bad_URI]

        return bad_nodes
