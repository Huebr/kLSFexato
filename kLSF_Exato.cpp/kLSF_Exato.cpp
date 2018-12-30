#include <iostream>                  // for std::cout
#include <utility>                   // for std::pair
#include <algorithm>                 // for std::for_each
#include <boost/graph/graph_traits.hpp> // for creation of descriptors vertex and edges.
#include <boost/graph/adjacency_list.hpp> //for usage of adjacency list
#include <boost/graph/filtered_graph.hpp>
#include <boost/graph/connected_components.hpp>
#include <boost/dynamic_bitset.hpp>
#include <unordered_set>

//needs a lot of optimization
//limpar typedef
//add new kind of graph with function number of colors
using namespace boost;

//basic definitions
typedef typename boost::dynamic_bitset<> db;

template <typename EdgeColorMap,typename ValidColorsMap>
struct valid_edge_color {
	valid_edge_color() { }
	valid_edge_color(EdgeColorMap color, ValidColorsMap v_colors) : m_color(color),v_map(v_colors) { }
	template <typename Edge>
	bool operator()(const Edge& e) const {
		return v_map.test(get(m_color, e));
	}
	EdgeColorMap m_color;
	ValidColorsMap v_map;
};




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
int max_reduce(Graph &g,int n_curr,int n_colors, std::vector<int> &comp,int label) {
	std::vector<int> parent(n_curr),level(n_curr);
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
			if(root(comp_a,parent)!= root(comp_b,parent)){
				if (level[root(comp_a,parent)] > level[root(comp_b,parent)]) parent[root(comp_b,parent)] = root(comp_a,parent);
				else {
					if (level[root(comp_a,parent)] == level[root(comp_b,parent)]) {
						level[root(comp_b,parent)]++;
					}
					parent[root(comp_a,parent)] = root(comp_b,parent);
				}
				result++;
			}
		}
		++it;
	}
	return result;
}

template<class Mask,class Graph>
Mask solvekLSFBB(Mask mask_curr, Mask mask_opt,int &n_colors,int d,Graph &g,const int &k) {
	if (d >= n_colors) return mask_opt;
	typedef typename property_map<Graph, edge_color_t>::type EdgeColorMap;
	typedef filtered_graph<Graph, valid_edge_color<EdgeColorMap, db> > fg;
	valid_edge_color<EdgeColorMap, Mask> filter_curr(get(edge_color, g), mask_curr);
	valid_edge_color<EdgeColorMap, Mask> filter_opt(get(edge_color, g), mask_opt);
	std::vector<int> components_curr(num_vertices(g)), components_opt(num_vertices(g));
	fg H_curr(g,filter_curr),H_opt(g,filter_opt);
	int n_curr, n_opt;
	n_curr = connected_components(H_curr,&components_curr[0]);
	n_opt = connected_components(H_opt, &components_opt[0]);
	volatile int n1,n2,max;
	n1 = mask_opt.count();
	n2 = mask_curr.count();
	if (mask_curr.count() == k) {
		if (n_curr<n_opt) {
			mask_opt = mask_curr;
			n_opt = n_curr;
			if (n_opt == 1) { 
				std::cout << "Bound by optimality: "<< mask_opt.count() << std::endl;
				exit(EXIT_SUCCESS);
			}
			return mask_opt;
		}
	}
	if (n_colors - d < k - mask_curr.count()) 	return mask_opt;
    max = max_reduce(g, n_curr, n_colors, components_curr, d);
	if ((n_curr - max) >= n_opt) return mask_opt;

	mask_curr.set(d);
	mask_opt = solvekLSFBB(mask_curr,mask_opt, n_colors, d + 1, g, k);
	mask_curr.flip(d);
	mask_opt = solvekLSFBB(mask_curr,mask_opt, n_colors, d + 1, g, k);
	return mask_opt;
}

template<class Graph,class Mask>
void print_filtered_graph(Graph &g,Mask valid) { //pay atention to the position of the bits and the colors positions in array
	typedef typename property_map<Graph, edge_color_t>::type EdgeColorMap;
	typedef typename boost::dynamic_bitset<> db;
	typedef filtered_graph<Graph, valid_edge_color<EdgeColorMap, db> > fg;

	valid_edge_color<EdgeColorMap,Mask> filter(get(edge_color, g),valid);
	fg tg(g, filter);
	print_edges(edges(tg).first, edges(tg).second,tg);
}


int main()
{
	enum { A, B, C, D, E, F, G, H };
	typedef adjacency_list<vecS, vecS, undirectedS, no_property, property<edge_color_t, int>> Graph;
	typedef std::pair<int, int> Edge;
	Graph::edge_iterator it, end;
	const int n_vertices = 14;
	const int k = 4;
	Edge edge_array[] = {
		Edge(1,2),  Edge(1,12), Edge(2,3),  Edge(3,4),
		Edge(4,5),  Edge(5,6),  Edge(5,8),  Edge(5,9),
		Edge(5,11), Edge(5,13), Edge(6,7),  Edge(7,8),
		Edge(8,9),  Edge(9,10), Edge(10,11),Edge(11,12),
		Edge(12,13),
	};
	int n_edges = sizeof(edge_array) / sizeof(edge_array[0]);
	const int colors[] = { H,H,D,D,C,F,E,D,C,F,G,E,A,B,G,A,B };

	Graph g(edge_array, edge_array + n_edges, colors, n_vertices);
	//add edges to super source vertex index 0. remember!!!
	std::unordered_set<int> st(colors, colors + sizeof(colors) / sizeof(colors[0]));
	int n_colors = st.size();
	st.clear();
	//for (int i = 1; i < n_vertices; ++i) boost::add_edge(0, i, property<edge_color_t, int>(n_colors + i - 1), g);
	std::tie(it, end) = boost::edges(g);
	print_edges(it, end, g);
	//temporario contar numero de cores
	//n_colors += n_vertices - 1;
	boost::dynamic_bitset<> mask_curr(n_colors); //all 0's by default
	boost::dynamic_bitset<> mask_opt(n_colors);
	int d = 0;
	mask_opt = solvekLSFBB(mask_curr, mask_opt,n_colors,d,g,k);
	print_filtered_graph(g, mask_opt);
	return 0;
}





