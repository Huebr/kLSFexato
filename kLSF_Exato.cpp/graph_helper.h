
// for std::for_each
#include <boost/graph/graph_traits.hpp> // for creation of descriptors vertex and edges.
#include <boost/graph/filtered_graph.hpp>
#include <boost/graph/connected_components.hpp>
#include <boost/dynamic_bitset.hpp>
#include <boost/graph/incremental_components.hpp>
#include <boost/pending/disjoint_sets.hpp>
#include <vector>

using namespace boost;
typedef typename boost::dynamic_bitset<> db;

template <typename EdgeColorMap, typename ValidColorsMap>
struct valid_edge_color {
	valid_edge_color() { }
	valid_edge_color(EdgeColorMap color, ValidColorsMap v_colors) : m_color(color), v_map(v_colors) { }
	template <typename Edge>
	bool operator()(const Edge& e) const {
		return v_map.test(get(m_color, e));
	}
	EdgeColorMap m_color;
	ValidColorsMap v_map;
};

// preprocessing functions
template<class Graph>
Graph MCR(Graph& g, int n_colors) {
	Graph result(num_vertices(g));
	typedef boost::graph_traits<Graph>::edge_descriptor edge_t;
	typedef typename property_map<Graph, edge_color_t>::type EdgeColorMap;
	typedef filtered_graph<Graph, valid_edge_color<EdgeColorMap, db> > fg;
	typedef typename fg::edge_iterator eit;
	eit it, end;
	for (int l = 0; l < n_colors; ++l) {
		db mask(n_colors);
		mask.set(l);
		valid_edge_color<EdgeColorMap, db> filter(get(edge_color, g), mask);
		fg H(g, filter);
		typedef typename property_map<fg, vertex_index_t>::type IndexMap;
		IndexMap index = get(vertex_index, H);
		//disjoint_sets ds(num_vertices(g))
		typedef std::map<int, std::size_t> rank_t; // => order on Element
		typedef std::map<int, int> parent_t;
		rank_t rank_map;
		parent_t parent_map;
		boost::associative_property_map<rank_t>   rank_pmap(rank_map);
		boost::associative_property_map<parent_t> parent_pmap(parent_map);
		boost::disjoint_sets<
			associative_property_map<rank_t>,
			associative_property_map<parent_t> > ds(
				rank_pmap,
				parent_pmap);
		//std::vector<Element> elements;
		//elements.push_back(Element(...));
		//rank_t rank_map;
		//parent_t parent_map;

		//boost::associative_property_map<rank_t>   rank_pmap(rank_map);
		//boost::associative_property_map<parent_t> parent_pmap(parent_map);

		for (int i = 0; i < num_vertices(g); ++i) {
			ds.make_set(i);
		}
		std::tie(it, end) = edges(H);
		while (it != end) {
			int u = index[source(*it, H)];
			int v = index[target(*it, H)];
			if (ds.find_set(u) != ds.find_set(v)) {
				add_edge(u, v, property<edge_color_t, int>(l), result);
				ds.union_set(u, v);
			}
			else {
				std::cout << "MCR removed edge:" << " (" << u << "," << v << ") " << " Color: " << l << std::endl;
			}
			++it;
		}
	}
	g.clear();
	return result;
}

//template function to print edges.
template<class EdgeIter, class Graph>
void print_edges(EdgeIter first, EdgeIter last, const Graph& G) {
	typedef typename property_map<Graph, edge_color_t>::const_type ColorMap;
	ColorMap colors = get(edge_color, G);
	//make color type generic
	//typedef typename property_traits<ColorMap>::value_type ColorType;
	//ColorType edge_color;
	for (auto it = first; it != last; ++it) {
		std::cout << "Edge: " << "(" << source(*it, G) << "," << target(*it, G) << ") " << " Color: " << colors[*it] << "\n";
		std::cout << "Edge: " << "(" << target(*it, G) << "," << source(*it, G) << ") " << " Color: " << colors[*it] << "\n";
	}
	std::cout << " Number of vertex: " << num_vertices(G) << std::endl;
	std::cout << " Number of edges: " << num_edges(G) << std::endl;
	std::vector<int> components(num_vertices(G));
	int num = connected_components(G, &components[0]);
	std::vector<int>::size_type i;
	std::cout << "Total number of components: " << num << std::endl;
	for (i = 0; i != components.size(); ++i)
		std::cout << "Vertex " << i << " is in component " << components[i] << std::endl;
	std::cout << std::endl;
}


int root(int current, std::vector<int> &parent) {
	while (parent[current] != current) {
		current = parent[current];
	}
	return current;
}


template<class Graph>
int max_reduce(Graph &g, int n_curr, int n_colors, std::vector<int> &comp, int label) {
	std::vector<int> parent(n_curr), level(n_curr);
	volatile int comp_a, comp_b; //so i could debug dont know why.
	int result;
	for (int i = 0; i < n_curr; ++i) {
		parent[i] = i;
		level[i] = 0;
	}
	result = 0;

	typedef typename property_map<Graph, edge_color_t>::type EdgeColorMap;
	typedef filtered_graph<Graph, valid_edge_color<EdgeColorMap, db> > fg;
	typedef typename fg::edge_iterator eit;
	eit it, end;
	db mask(n_colors);
	mask.set(label);
	valid_edge_color<EdgeColorMap, db> filter(get(edge_color, g), mask);
	fg G(g, filter);
	std::tie(it, end) = boost::edges(G);

	while (it != end) {
		comp_a = comp[source(*it, G)];
		comp_b = comp[target(*it, G)];
		if (comp_a != comp_b) {
			volatile int root_a, root_b;
			root_a = root(comp_a, parent);
			root_b = root(comp_b, parent);
			if (root(comp_a, parent) != root(comp_b, parent)) {
				if (level[root(comp_a, parent)] > level[root(comp_b, parent)]) parent[root(comp_b, parent)] = root(comp_a, parent);
				else {
					if (level[root(comp_a, parent)] == level[root(comp_b, parent)]) {
						level[root(comp_b, parent)]++;
					}
					parent[root(comp_a, parent)] = root(comp_b, parent);
				}
				result++;
			}
		}
		++it;
	}
	return result;
}

template<class Graph, class Mask>
int get_components(Graph &g, Mask &m, std::vector<int> &components) {
	typedef typename property_map<Graph, edge_color_t>::type EdgeColorMap;
	typedef typename boost::dynamic_bitset<> db;
	typedef filtered_graph<Graph, valid_edge_color<EdgeColorMap, db> > fg;
	valid_edge_color<EdgeColorMap, Mask> filter(get(edge_color, g), m);
	fg tg(g, filter);
	int num = connected_components(tg, &components[0]);
	return num;
}

//MVCA modified always has k colors
template <class Graph>
int kLSFMVCA(Graph &g, int k_sup, int n_labels) {
	std::vector<int> components(num_vertices(g));
	db temp(n_labels);
	int num_c = get_components(g, temp, components);
	int num_c_best = num_c;
	while (temp.count() < k_sup) {
		int best_label = 0;
		for (int i = 0; i < n_labels; ++i) {
			if (!temp.test(i)) {
				temp.set(i);
				int nc = get_components(g, temp, components);
				if (nc <= num_c_best) {
					num_c_best = nc;
					best_label = i;
				}
				temp.flip(i);
			}
		}
		temp.set(best_label);
	}
	num_c_best = get_components(g, temp, components);
	//print_filtered_graph(g,temp);
	return  num_c_best;//just to be right
}


template<class Graph, class Mask>
void print_filtered_graph(Graph &g, Mask valid) { //pay atention to the position of the bits and the colors positions in array
	typedef typename property_map<Graph, edge_color_t>::type EdgeColorMap;
	typedef typename boost::dynamic_bitset<> db;
	typedef filtered_graph<Graph, valid_edge_color<EdgeColorMap, db> > fg;

	valid_edge_color<EdgeColorMap, Mask> filter(get(edge_color, g), valid);
	fg tg(g, filter);
	print_edges(edges(tg).first, edges(tg).second, tg);
}