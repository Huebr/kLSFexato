#include <iostream>                  // for std::cout
#include <utility>                   // for std::pair
#include <algorithm>                 // for std::for_each
#include <boost/graph/graph_traits.hpp> // for creation of descriptors vertex and edges.
#include <boost/graph/adjacency_list.hpp> //for usage of adjacency list
#include <boost/graph/filtered_graph.hpp>
#include <boost/graph/connected_components.hpp>
#include <boost/dynamic_bitset.hpp>
#include <boost/graph/graphml.hpp>
#include <boost/dynamic_bitset.hpp>
#include <boost/program_options.hpp>
#include <boost/algorithm/string/split.hpp>
#include <boost/algorithm/string/classification.hpp>
#include <boost/algorithm/string/trim.hpp>
#include <boost/exception/all.hpp>
#include <exception>
#include <vector>
#include <string>

//needs a lot of optimization
//limpar typedef
//add new kind of graph with function number of colors
using namespace boost;
namespace po = boost::program_options;

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
Mask solvekLSFBB(Mask mask_curr, Mask mask_opt, int &n_colors, int d, Graph &g, const int &k) {
	if (d >= n_colors) return mask_opt;
	typedef typename property_map<Graph, edge_color_t>::type EdgeColorMap;
	typedef filtered_graph<Graph, valid_edge_color<EdgeColorMap, db> > fg;
	valid_edge_color<EdgeColorMap, Mask> filter_curr(get(edge_color, g), mask_curr);
	valid_edge_color<EdgeColorMap, Mask> filter_opt(get(edge_color, g), mask_opt);
	std::vector<int> components_curr(num_vertices(g)), components_opt(num_vertices(g));
	fg H_curr(g, filter_curr), H_opt(g, filter_opt);
	int n_curr, n_opt;
	n_curr = connected_components(H_curr, &components_curr[0]);
	n_opt = connected_components(H_opt, &components_opt[0]);
	volatile int n1, n2, max;
	n1 = mask_opt.count();
	n2 = mask_curr.count();
	if (mask_curr.count() == k) {
		if (n_curr < n_opt) {
			mask_opt = mask_curr;
			n_opt = n_curr;
			if (n_opt == 1) {
				std::cout << "Bound by optimality: " << mask_opt.count() << std::endl;//substituir goto
				exit(EXIT_SUCCESS);
			}
			return mask_opt;
		}
	}
	if (n_colors - d < k - mask_curr.count()) 	return mask_opt;
	max = 0;
	if (k - mask_curr.count() > 0) {
		std::vector<int> tmp(k - mask_curr.count());
		for (int i = 0; d + i < n_colors; ++i) { // need to consider all labels undecided
			max = max_reduce(g, n_curr, n_colors, components_curr, d + i);
			for (int i = 0; i < k - mask_curr.count(); ++i) {
				if (max > tmp[i]) tmp[i] = max;
			}
		}
		for (int i = 0; i < k - mask_curr.count(); ++i) {
		max += tmp[i];
		}
	}
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



int main(int argc, const char *argv[])
{
	typedef adjacency_list<vecS, vecS, undirectedS, no_property, property<edge_color_t, int>> Graph;
	typedef std::pair<int, int> Edge;
	typedef boost::graph_traits<Graph>::vertex_descriptor vertex_t;
	Graph::edge_iterator it, end;
	Graph g;
	int n_vertices, n_colors;
	//command-line processor

	try {
		std::ifstream ifn;
		po::options_description desc{ "Options" };
		desc.add_options()("help,h", "produce help message")
			("input-file,i", po::value< std::string >(), "input file")
			("include-path,I", po::value< std::string >(), "include path")
			("setup-file", po::value< std::string >(), "setup file");
		po::positional_options_description p;
		p.add("input-file", -1);


		po::variables_map vm;
		po::store(po::command_line_parser(argc, argv).
			options(desc).positional(p).run(), vm);
		po::notify(vm);

		if (vm.count("help")) {
			std::cout << desc << "\n";
			return 1;
		}
		else if (vm.count("input-file"))
		{
			std::cout << "Input files are: " << vm["input-file"].as<std::string>() << "\n";
			if (vm.count("include-path"))ifn.open((vm["include-path"].as<std::string>() + vm["input-file"].as<std::string>()).c_str(), std::ifstream::in);
			else ifn.open(vm["input-file"].as<std::string>().c_str(), std::ifstream::in);
			if (!ifn.is_open()) {
				std::cout << "error opening file" << std::endl;
				exit(EXIT_FAILURE);
			}
			dynamic_properties dp;
			dp.property("color", get(edge_color, g));
			read_graphml(ifn, g, dp);

			std::vector<std::string> vecI;
			split(vecI, vm["input-file"].as<std::string>(), is_any_of("-."), token_compress_off);
			if (vecI.size() == 6) {
				std::cout << vecI[0] << std::endl;
				n_vertices = std::stoi(vecI[0]);
				std::cout << vecI[2] << std::endl;
				n_colors = std::stoi(vecI[2]);
				std::cout << vecI[3] << std::endl;
				int k = std::stoi(vecI[3]);
				//add edges to super source vertex. remember!!!
				//vertex_t u = add_vertex(g);
				//n_vertices++;
				//for (int i = 0; i < n_vertices - 1; ++i) boost::add_edge(u, i, property<edge_color_t, int>(n_colors++), g);
				//std::tie(it, end) = boost::edges(g);
				//print_edges(it, end, g);
				boost::dynamic_bitset<> mask_curr(n_colors); //all 0's by default
				boost::dynamic_bitset<> mask_opt(n_colors);
				int d = 0;
				mask_opt = solvekLSFBB(mask_curr, mask_opt, n_colors, d, g, k);
				std::cout << "solutions color(s):";
				for (int i = 0; i < n_colors; ++i) {
					if (mask_opt.test(i))std::cout<<" "<<i;
				}
				std::cout << std::endl;
				print_filtered_graph(g, mask_opt);
			}
			else {
				std::cout << "file wrong name format." << std::endl;
			}

		}
		else if (vm.count("setup-file")) {
			std::cout << "Not implemented yet" << std::endl;
		}
		else {
			std::cout << "see options(-h)." << std::endl;
		}


	}
	catch (const po::error &ex) {
		std::cout << ex.what();
		exit(EXIT_FAILURE);
	}
	catch (boost::exception &ex) {
		std::cout << boost::diagnostic_information(ex) << std::endl;
	}
	catch (std::exception &ex) {
		std::cout << ex.what();
		exit(EXIT_FAILURE);
	}

	return 0;
}



