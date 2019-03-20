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

//temporary

#define MAX_SIZE 2000

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

 //tbb::atomic<db> g_mask_opt;
 tbb::atomic<int> g_n_opt;



 
 
 // preprocessing functions
 template<class Graph>
 Graph MCR(Graph& g, int n_colors) {
	 Graph result(num_vertices(g));
	 typedef boost::graph_traits<Graph>::edge_descriptor edge_t;
	 typedef typename property_map<Graph, edge_color_t>::type EdgeColorMap;
	 typedef filtered_graph<Graph, valid_edge_color<EdgeColorMap, db> > fg;
	 typedef typename fg::edge_iterator eit;
	 eit it,end;
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
				 int u = index[source(*it,H)];
				 int v = index[target(*it, H)];
				 if (ds.find_set(u)!= ds.find_set(v)) {
					 add_edge(u, v, property<edge_color_t, int>(l), result);
					 ds.union_set(u,v);
				 }
				 else {
					 std::cout<<"MCR removed edge:"<<" (" << u << "," << v << ") " << " Color: " << l << std::endl;
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

template< class Graph>
db solvekLSFBB2(int &n_colors, Graph &g, const int &k , std::vector<std::pair<int, int>>& vecC) {
	typedef typename property_map<Graph, edge_color_t>::type EdgeColorMap;
	typedef filtered_graph<Graph, valid_edge_color<EdgeColorMap, db> > fg;
	std::vector<int> components(num_vertices(g));
	std::queue<node> frontier;
	int n_opt = num_vertices(g);
	db mask_opt(n_colors);
	node myInitialNode;
	myInitialNode.mask = db(n_colors);
	myInitialNode.depth = 0;
	frontier.push(myInitialNode);
	while (!frontier.empty()) {
		node curr = frontier.front();
		frontier.pop();
		if (n_opt == 1) return mask_opt;
		db mask_curr = curr.mask;
		int d = curr.depth;
		if (d >= n_colors) continue;
		valid_edge_color<EdgeColorMap, db> filter_curr(get(edge_color, g), mask_curr);
		fg H_curr(g, filter_curr);
		int n_curr = connected_components(H_curr, &components[0]);
		if (mask_curr.count() == k) {
			if (n_curr < n_opt) {
				mask_opt = mask_curr;
				n_opt = n_curr;
				continue;
			}
		}
		if (n_colors - d < k - mask_curr.count()) continue;
		int max = 0;
		//max reduce evaluation
		if (k - mask_curr.count() > 0) {
			std::vector<int> tmp;
			for (int i = 0; d + i < n_colors; ++i) { // need to consider all labels undecided
				max = max_reduce(g, n_curr, n_colors, components, vecC[d + i].first);
				tmp.push_back(max);
			}
			std::sort(tmp.begin(), tmp.end(), std::greater<int>());
			max = 0;
			for (int i = 0; i < k - mask_curr.count(); ++i) {
				max += tmp[i];
			}
		}
		if ((n_curr - max) >= n_opt) continue;
		mask_curr.set(vecC[d].first);
		frontier.push(node{mask_curr,d + 1 });
		mask_curr.flip(vecC[d].first);
		frontier.push(node{mask_curr,d + 1 });
	}	
	return mask_opt;
}

//first no colors answers
template<class Graph>
class node_parallel
{
public:
	node_parallel() : mask(), depth(), g(), vecC(), k() {}
	node_parallel(db m, int d, Graph &g, std::vector<std::pair<int, int>>& vecC, int k, int n_c)
		: mask(m), depth(d), g(g), vecC(vecC), k(k), n_colors(n_c) {}
	db mask;
	int k;
	std::vector<std::pair<int, int>> vecC;
	Graph g;
	int n_colors;
	int depth;
};
template<class Graph>
class Body {
public:
	Body() {};
	void operator()(node_parallel<Graph> item, tbb::parallel_do_feeder<node_parallel<Graph>> &feeder) const {
		typedef typename property_map<Graph, edge_color_t>::type EdgeColorMap;
		typedef filtered_graph<Graph, valid_edge_color<EdgeColorMap, db> > fg;
		std::vector<int> components(num_vertices(item.g));
		valid_edge_color<EdgeColorMap, db> filter(get(edge_color, item.g), item.mask);
		fg H_curr(item.g, filter);
		int n_curr = connected_components(H_curr, &components[0]);
		int n_opt = g_n_opt; //take a snapshot
		if (n_opt == 1) return;
		if (item.depth >= item.n_colors) return;
		if ((item.mask).count() == item.k) {//need to update properly using compare and swap
			do {
				n_opt = g_n_opt;
				if (n_opt <= n_curr) break;
			} while (g_n_opt.compare_and_swap(n_curr, n_opt) != n_opt);
			/*if (n_curr < n_opt) {
			g_mask_opt = mask_curr;
			g_n_opt = n_curr;
			return;
			}*/
		}
		if (item.n_colors - item.depth < item.k - (item.mask).count()) return;
		int max = 0;
		//max reduce evaluation
		if (item.k - (item.mask).count() > 0) {
			std::vector<int> tmp;
			for (int i = 0; item.depth + i < item.n_colors; ++i) { // need to consider all labels undecided
				max = max_reduce(item.g, n_curr, item.n_colors, components, (item.vecC[item.depth + i]).first);
				tmp.push_back(max);
			}
			std::sort(tmp.begin(), tmp.end(), std::greater<int>());
			max = 0;
			for (int i = 0; i < item.k - (item.mask).count(); ++i) {
				max += tmp[i];
			}
		}
		n_opt = g_n_opt;
		if ((n_curr - max) >= n_opt) return;
		(item.mask).set((item.vecC[item.depth]).first);
		feeder.add(node_parallel<Graph>{ item.mask, item.depth + 1, item.g, item.vecC, item.k, item.n_colors});
		(item.mask).flip((item.vecC[item.depth]).first);
		feeder.add(node_parallel<Graph>{ item.mask, item.depth + 1, item.g, item.vecC, item.k, item.n_colors});
		return;
	}
};
template< class Graph> // trying no print mask first
void solvekLSFBB3(int n_colors, Graph &g, const int &k, std::vector<std::pair<int, int>>& vecC) {
	tbb::concurrent_vector<node_parallel<Graph>> concurrent_v;
	db mask(n_colors);
	node_parallel<Graph> first_no(mask, 0, g, vecC, k, n_colors);
	concurrent_v.push_back(first_no);
	g_n_opt = num_vertices(g);
	Body<Graph> body;
	tbb::tick_count t0 = tbb::tick_count::now();
	tbb::parallel_do(concurrent_v, body);
	tbb::tick_count t1 = tbb::tick_count::now();
	std::cout<<"time for action = "<< (t1 - t0).seconds()<<"seconds."<<std::endl;
	std::cout << "result =  " << g_n_opt << std::endl;
}


template<class Mask,class Graph>
Mask solvekLSFBB(Mask mask_curr, Mask mask_opt, int &n_colors,std::vector<std::pair<int,int>>& vecC, int d, Graph &g, const int &k) {
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
	if (n_opt == 1) return mask_opt;
	int n1, n2, max;
	if (mask_curr.count() == k) {
		if (n_curr < n_opt) {
			mask_opt = mask_curr;
			n_opt = n_curr;
			return mask_opt;
		}
	}
	if (n_colors - d < k - mask_curr.count()) 	return mask_opt;
	max = 0;
	//clock_t diff;
	//diff = clock();
	//max reduce evaluation
	if (k - mask_curr.count() > 0) {
		std::vector<int> tmp;
		for (int i = 0; d + i < n_colors; ++i) { // need to consider all labels undecided
			max = max_reduce(g, n_curr, n_colors, components_curr, vecC[d + i].first);
			tmp.push_back(max);
		}
		std::sort(tmp.begin(),tmp.end(), std::greater<int>());
		max = 0;
		for (int i = 0; i < k - mask_curr.count(); ++i) {
			max += tmp[i];
		}
	}
	if ((n_curr - max) >= n_opt) return mask_opt;

	mask_curr.set(vecC[d].first);
	mask_opt = solvekLSFBB(mask_curr,mask_opt, n_colors,vecC, d + 1, g, k);
	mask_curr.flip(vecC[d].first);
	mask_opt = solvekLSFBB(mask_curr,mask_opt, n_colors,vecC, d + 1, g, k);
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

			std::vector<std::string> vecI;
			split(vecI, vm["input-file"].as<std::string>(), is_any_of("-."), token_compress_off);
			if (vecI.size() == 6) {
				std::cout <<"n_vertices: "<< vecI[0] << std::endl;
				n_vertices = std::stoi(vecI[0]);
				std::cout << "n_colors: " << vecI[2] << std::endl;
				n_colors = std::stoi(vecI[2]);
				std::cout << "k: " << vecI[3] << std::endl;
				int k = std::stoi(vecI[3]);
				//add edges to super source vertex. remember!!!
				//vertex_t u = add_vertex(g);
				//n_vertices++;
				//for (int i = 0; i < n_vertices - 1; ++i) boost::add_edge(u, i, property<edge_color_t, int>(n_colors++), g);
				//std::tie(it, end) = boost::edges(g);
				//print_edges(it, end, g);
				boost::dynamic_bitset<> mask_curr(n_colors); //all 0's by default
				boost::dynamic_bitset<> mask_opt(n_colors);
				std::tie(it, end) = boost::edges(g);
				auto colormap = get(edge_color, g);
				std::vector<int> edges_per_color(n_colors);
				while (it != end) {
					edges_per_color[colormap[*it]]++;
					++it;
				}
				for (int i = 0; i < n_colors;++i) {
					cores.push_back(std::pair<int, int>(i, edges_per_color[i]));
				}
				std::sort(cores.begin(), cores.end(),compFunctor);
				/*print_edges(edges(g).first, edges(g).second,g);
				copy_graph(MCR(g,n_colors),g);
				print_edges(edges(g).first, edges(g).second, g);
				*/
				//for (auto it = cores.begin(); it != cores.end(); ++it) std::cout << (*it).first <<" "<< (*it).second << std::endl;
				
				solvekLSFBB3(n_colors, g, k, cores);
				int d = 0;
				clock_t t;
				double time;
				t = clock();
				mask_opt = solvekLSFBB2(n_colors, g, k, cores);
				t = clock()-t;
				time = (double)t / CLOCKS_PER_SEC;
				std::cout << "solutions color(s):";
				for (int i = 0; i < n_colors; ++i) {
					if (mask_opt.test(i))std::cout<<" "<<i;
				}
				std::cout << std::endl<<"time(seconds): "<<time<< std::endl;
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



