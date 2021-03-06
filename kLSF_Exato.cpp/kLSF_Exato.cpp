#include <iostream>                  // for std::cout
#include <utility>                   // for std::pair
#include <algorithm>                 // for std::for_each
#include <boost/graph/graph_traits.hpp> // for creation of descriptors vertex and edges.
#include <boost/graph/adjacency_list.hpp> //for usage of adjacency list
#include <boost/graph/filtered_graph.hpp>
#include <boost/graph/copy.hpp>
#include <tbb/task_scheduler_init.h>
#include <tbb/parallel_do.h>
#include <boost/graph/connected_components.hpp>
#include <boost/dynamic_bitset.hpp>
#include <boost/graph/graphml.hpp>
#include <boost/dynamic_bitset.hpp>
#include <boost/graph/incremental_components.hpp>
#include <boost/program_options.hpp>
#include <boost/algorithm/string/split.hpp>
#include <boost/pending/disjoint_sets.hpp>
#include <boost/algorithm/string/classification.hpp>
#include <boost/algorithm/string/trim.hpp>
#include <boost/exception/all.hpp>
#include <ctime>
#include <map>
#include <exception>
#include <vector>
#include <queue>
#include <string>
#include <tbb/atomic.h>
#include <tbb/tick_count.h>
#include <tbb/parallel_do.h>
#include <tbb/concurrent_vector.h>
#include "graph_helper.h"

//need to add lots of optimization
//limpar typedef
//add new kind of graph with function number of colors
using namespace boost;
namespace po = boost::program_options;
//basic definitions
typedef typename boost::dynamic_bitset<> db;

// Declaring the type of Predicate that accepts 2 pairs and return a bool
typedef std::function<bool(std::pair<int, int>, std::pair<int, int>)> Comparator;

//new structures make easier
 class node
{
public:
	node() : mask(), depth() {}
    node (db m, int d)
	: mask(m), depth(d) {}
 db mask;
 int depth;
};

template<class Graph,class EdgeIter>
void helper_filter(Graph &g,EdgeIter &it,EdgeIter &end,int n,int d) {//temporary using filtered graph trick
	typedef typename property_map<Graph, edge_color_t>::type EdgeColorMap;
	typedef filtered_graph<Graph, valid_edge_color<EdgeColorMap, db> > fg;
	db mask(n);
	mask.set(d);
	valid_edge_color<EdgeColorMap, Mask> filter(get(edge_color, g), mask);
	fg G(g, filter);
	std:tie(it, end) = edges(G);
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

template<class Graph, class Mask>
int max_reduce(Graph,&g,int n_curr,int n_colors, std::vector<int> &comp,int label) {
	std::vector<int> parent(n_curr),level(n_curr);
	typedef typename graph_traits<Graph>::EdgeIterator eit;
	eit it, end;
	int result;
	for (int i = 0; i < n_curr; ++i) {
		parent[i] = 0;
		level[i] = 0;
	}
	result = 0;
	helper_filter(g,it,end,n_colors,label);
	//parei aqui
}


template<class Mask,class Graph>
Mask solvekLSFBB(Mask mask_curr, Mask mask_opt, int &n_colors,std::vector<std::pair<int,int>>& vecC, int d, Graph &g, const int &k) {
	if (d >= n_colors) return mask_opt;
	typedef typename property_map<Graph, edge_color_t>::type EdgeColorMap;
	typedef filtered_graph<Graph, valid_edge_color<EdgeColorMap, db> > fg;
	valid_edge_color<EdgeColorMap, Mask> filter_curr(get(edge_color, g), mask_curr);
	valid_edge_color<EdgeColorMap, Mask> filter_opt(get(edge_color, g), mask_opt);
	std::vector<int> components_curr, components_opt;
	Mask temp_mask(n_colors);
	fg H_curr(g,filter_curr),H_opt(g,filter_opt);
	int n_curr, n_opt;
	n_curr = connected_components(H_curr,components_curr);
	n_opt = connected_components(H_opt, components_opt);
	if (mask_curr.count() == k) {
		if (n_curr < n_opt) {
			mask_opt = mask_curr;
			n_opt = n_curr;
			if (n_opt == 1) { // n_opt = n_curr
				std::cout << mask_opt.count() << endl;
				exit(EXIT_SUCCESS);
			}
			return mask_opt;
		}
	}
	if (n_colors - d > k + mask_curr.count()) return mask_opt;
	if (n_curr - max_reduce(g,n_curr,n_colors,components_curr,d+1)>=n_opt) return mask_opt;
	mask_curr.set(d);
	mask_opt = solvekLSFBB(mask_curr,mask_opt, n_colors, d + 1, g, k);
	mask_curr.flip(d);
	mask_opt = solvekLSFBB(mask_curr,mask_opt, n_colors, d + 1, g, k);
	return mask_opt;
}




int main(int argc, const char *argv[])
{
	typedef adjacency_list<vecS, vecS, undirectedS, no_property, property<edge_color_t, int>> Graph;
	typedef std::pair<int, int> Edge;
	typedef boost::graph_traits<Graph>::vertex_descriptor vertex_t;
	tbb::task_scheduler_init init;
	Graph::edge_iterator it, end;
	Graph g;
	int n_vertices, n_colors;
	std::vector<std::pair<int, int>> cores;
	//command-line processor
	// Defining a lambda function to compare two pairs. It will compare two pairs using second field
	Comparator compFunctor = [](std::pair<int, int> elem1, std::pair<int, int> elem2)
	{
		return elem1.second > elem2.second;
	};
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
			if (vm.count("include-path")) {
				ifn.open((vm["include-path"].as<std::string>() + vm["input-file"].as<std::string>()).c_str(), std::ifstream::in);
				std::cout << "Include path is: " << vm["include-path"].as<std::string>() << "\n";
			}
			else ifn.open(vm["input-file"].as<std::string>().c_str(), std::ifstream::in);
			if (!ifn.is_open()) {
				std::cout << "error opening file" << std::endl;
				exit(EXIT_FAILURE);
			}
			dynamic_properties dp;
			dp.property("color", get(edge_color, g));
			read_graphml(ifn, g, dp);

	Graph g(edge_array, edge_array + n_edges, colors, n_vertices);
	//add edges to super source vertex index 0. remember!!!
	std::unordered_set<int> st(colors, colors + sizeof(colors) / sizeof(colors[0]));
	int n_colors = st.size();
	st.clear();
	for (int i = 1; i < n_vertices; ++i) boost::add_edge(0, i, property<edge_color_t, int>(n_colors + i - 1), g);
	std::tie(it, end) = boost::edges(g);
	print_edges(it, end, g);
	//temporario contar numero de cores
	n_colors += n_vertices - 1;
	boost::dynamic_bitset<> mask_curr(n_colors); //all 0's by default
	boost::dynamic_bitset<> mask_opt(n_colors);
	int d = 0;
	mask_opt.set(2);
	mask_opt.set(3);
	mask_opt.set(5);
	mask_opt.set(7);
	print_filtered_graph(g,mask_opt);
	//mask_opt = solvekLSFBB(mask_curr, mask_opt,n_colors,d,g,k);
	return 0;
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



