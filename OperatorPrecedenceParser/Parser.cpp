/* 1552212 端启航 信息安全 */
#include <iostream>
#include <string>
#include <vector>
#include <sstream>
#include <map>
#include <cctype>
#include <stack>
#include <algorithm>
#include <set>
#include <iomanip>
#define FIRSTVT true
#define LASTVT false
using namespace std;
typedef vector<char> gramma_item_t;
typedef vector<gramma_item_t> gramma_items_t;
typedef pair<char, gramma_items_t> gramma_pair_t;
typedef map<char, vector<char>> vt_set_t;

class TreeNode
{
public:
	char value;
	vector<TreeNode*> children;

	TreeNode(const char ch) : value(ch)
	{}
};

void error(const string& msg)
{
	cout << msg << endl;
	system("pause");
	exit(1);
}

/**
 * \brief 判断是否是终结符
 * \param ch 
 * \return true:终结符 false:非终结符
 */
inline bool TerminalSymbolQ(const char ch)
{
	if (!isupper(ch))
		return true;
	return false;
}

/**
 * \brief 获取输入放入gramma中
 * \param gramma 文法
 */
void GetInput(vector<gramma_pair_t>& gramma)
{
	while (true)
	{
		string input_temp;
		getline(cin, input_temp);
		if (input_temp.front() == '#')
			break;

		if (input_temp.find("->") == string::npos)
			error("输入错误!");
		replace(input_temp.begin(), input_temp.end(), '|', ' ');
		stringstream ss(input_temp.substr(0, input_temp.find_first_of("->")));
		gramma_pair_t gramma_pair;
		ss >> gramma_pair.first;
		stringstream ss2(input_temp.substr(input_temp.find_first_of("->") + 2));
		gramma_items_t gramma_items;
		string temp;
		while (ss2 >> temp)
		{
			gramma_item_t gramma_item;
			for (auto v : temp)
			{
				if (!gramma_item.empty() && !TerminalSymbolQ(gramma_item.back()) && !TerminalSymbolQ(v))
					error("非算符文法!");
				gramma_item.push_back(v);
			}
			gramma_items.push_back(gramma_item);
		}
		gramma_pair.second = gramma_items;
		gramma.push_back(gramma_pair);
	}
}

/**
 * \brief 查找FIRSTVT或LASTVT
 * \param gramma 文法
 * \param order 找FIRSTVT还是LASTVT
 * \return 
 */
vt_set_t FindVT(vector<gramma_pair_t> gramma, const bool order)
{
	vt_set_t vt_set;
	map<char, map<char, bool>> Fmatrix;
	stack<pair<char, char>> pair_stack;
	for (auto gramma_pair : gramma)// 对于文法的每一项
		for (auto str : gramma_pair.second)// 对于每一个产生式
		{
			if (order == LASTVT)
				reverse(str.begin(), str.end());
			bool first_b = true;
			for (auto ch : str)
				if (TerminalSymbolQ(ch) && first_b)// terminal and first
				{
					first_b = false;
					Fmatrix[gramma_pair.first][ch] = true;
					pair_stack.push(pair<char, char>(gramma_pair.first, ch));
				}
				else
					Fmatrix[gramma_pair.first][ch] = false;
		}
	while (!pair_stack.empty())
	{
		pair<char, char> temp = pair_stack.top();
		pair_stack.pop();
		for (auto gramma_pair : gramma)
			for (auto str : gramma_pair.second)
			{
				if (order == LASTVT)
					reverse(str.begin(), str.end());
				if (str.front() == temp.first && temp.first != gramma_pair.first)
				{
					Fmatrix[gramma_pair.first][temp.second] = true;
					pair_stack.push(pair<char, char>(gramma_pair.first, temp.second));
				}
			}
	}
	for (auto nt : Fmatrix)
		for (const auto vt : nt.second)
			if (vt.second == true)
				vt_set[nt.first].push_back(vt.first);
	return vt_set;
}

/**
 * \brief 获得优先级表
 * \param gramma 文法
 * \param first_vt FIRST集
 * \param last_vt LAST集
 * \return 优先级表
 */
map<char, map<char, int>> GetRelationshipTable(const vector<gramma_pair_t>& gramma, const vt_set_t& first_vt,
                                               const vt_set_t& last_vt)
{
	set<char> all_vt;
	map<char, map<char, int>> relationship_table;
	for (auto gramma_pair : gramma)// 对于文法的每一项
		for (gramma_item_t str : gramma_pair.second)// 对于每一个产生式
		{
			if (TerminalSymbolQ(str.front()))
				all_vt.insert(str.front());
			if (str.size() == 1)
				continue;
			for (gramma_item_t::iterator it = str.begin(); it != str.end() - 1; ++it)
			{
				if (TerminalSymbolQ(*it))
					all_vt.insert(*it);
				if (TerminalSymbolQ(*(it + 1)))
					all_vt.insert(*(it + 1));
				//  IF  Xi和Xi+1均为终结符  THEN  置Xi = Xi+1
				if (TerminalSymbolQ(*it) && TerminalSymbolQ(*(it + 1)))
				{
					if (relationship_table.find(*it) != relationship_table.end() &&
						relationship_table[*it].find(*(it + 1)) != relationship_table[*it].end())
						error("非算符优先文法！");
					relationship_table[*it][*(it + 1)] = 0;
				}
				//  IF  i<n-2且Xi和Xi+2都为终结符
				// 但Xi + 1为非终结符  THEN  置Xi = Xi + 2；
				if (str.size() >= 3 && it <= str.end() - 3 && TerminalSymbolQ(*it) && !TerminalSymbolQ(
					*(it + 1)) && TerminalSymbolQ(*(it + 2)))
				{
					if (relationship_table.find(*it) != relationship_table.end() &&
						relationship_table[*it].find(*(it + 2)) != relationship_table[*it].end())
						error("非算符优先文法！");
					relationship_table[*it][*(it + 2)] = 0;
				}
				// IF  Xi为终结符而Xi+1为非终结符  THEN
				// FOR  FIRSTVT(Xi + 1)中的每个a  DO
				// 置 Xi < a；
				if (TerminalSymbolQ(*it) && !TerminalSymbolQ(*(it + 1)))
					for (auto a : first_vt.at(*(it + 1)))
					{
						if (relationship_table.find(*it) != relationship_table.end() &&
							relationship_table[*it].find(a) != relationship_table[*it].end())
							error("非算符优先文法！");
						relationship_table[*it][a] = -1;
					}
				// IF  Xi为非终结符而Xi+1为终结符  THEN
				// FOR  LASTVT(Xi)中的每个a   DO
				// 置  a > Xi + 1
				if (!TerminalSymbolQ(*it) && TerminalSymbolQ(*(it + 1)))
					for (auto a : last_vt.at(*it))
					{
						if (relationship_table.find(a) != relationship_table.end() &&
							relationship_table[a].find(*(it + 1)) != relationship_table[a].end())
							error("非算符优先文法！");
						relationship_table[a][*(it + 1)] = 1;
					}
			}
		}
	for (const auto i : all_vt)
	{
		relationship_table['#'][i] = -1;
		relationship_table[i]['#'] = 1;
	}
	relationship_table['#']['#'] = 0;
	return relationship_table;
}

/**
 * \brief 查找最左素短语
 * \param cs 输入字符串
 * \param relationship_table 关系表
 * \return 最左素短语起始的iterator
 */
string::const_iterator FindLeftmostPrimePhrase(const string& cs, map<char, map<char, int>> relationship_table)
{
	// cs是倒过来的
	auto it = cs.end() - 1;
	auto next_nt = it;
	while (true)
	{
		if (*it == '#')
			return it + 1;
		if (!TerminalSymbolQ(*it))
		{
			--it;
			continue;
		}
		next_nt = it - 1;
		while (!TerminalSymbolQ(*next_nt))
			--next_nt;
		if (relationship_table.at(*next_nt).at(*it) == -1)
			break;
		--it;
	}
	return next_nt + 1;
}

/**
 * \brief 打印关系表
 * \param relationship_table 
 */
void PrintRelationshipTable(const map<char, map<char, int>>& relationship_table)
{
	cout << endl << "========优先关系表=======" << endl;

	vector<char> all_vt;
	for (const auto i : relationship_table)
		all_vt.push_back(i.first);
	cout << " ";
	for (const auto value : all_vt)
		cout << " " << value;
	cout << endl;
	for (const auto i : all_vt)
	{
		cout << i << " ";
		for (const auto j : all_vt)
			if (relationship_table.at(i).find(j) != relationship_table.at(i).end())
			{
				if (relationship_table.at(i).at(j) == -1)
					cout << "< ";
				else if (relationship_table.at(i).at(j) == 0)
					cout << "= ";
				else
					cout << "> ";
			}
			else
			{
				cout << "  ";
			}
		cout << endl;
	}
}

/**
 * \brief 打印first集和last集
 * \param first_vt 
 * \param last_vt 
 */
void PrintVT(const vt_set_t& first_vt, const vt_set_t& last_vt)
{
	cout << endl << "========FIRST集=======" << endl;

	for (auto value : first_vt)
	{
		cout << "FIRSTVT(" << value.first << ") = { ";
		for (auto second : value.second)
			cout << second << "  ";
		cout << '}' << endl;
	}
	cout << "========LAST集========" << endl;
	for (auto value : last_vt)
	{
		cout << "LASTVT(" << value.first << ") = { ";
		for (auto second : value.second)
			cout << second << "  ";
		cout << '}' << endl;
	}
}


/**
 * \brief 分析输入串
 * \param input 输入字符串
 * \param relationship_table 关系表
 * \return 语法分析树
 */
TreeNode* Analyze(string input, const map<char, map<char, int>>& relationship_table)
{
	vector<TreeNode*> nodes;
	string char_stack;

	cout << endl << "符号栈\t\t\t输入串\t\t\t关系\t\t\t操作\t\t\t最左素短语" << endl;
	// 由于要对input作为栈操作，需要倒置
	reverse(input.begin(), input.end());
	char_stack.push_back('#');
	while (!input.empty())
	{
		cout << setw(24) << left << char_stack;
		// input是倒置的，输出时需要反转一下
		reverse(input.begin(), input.end());
		cout << setw(24) << left << input;
		reverse(input.begin(), input.end());
		// char_stack是倒置的，end为栈顶
		auto stack_top = char_stack.end();
		while (!TerminalSymbolQ(*--stack_top));

		if (relationship_table.at(*stack_top).find(input.back()) == relationship_table.at(*stack_top).end())
			error("非文法的符号或无优先级");
		else if (relationship_table.at(*stack_top).at(input.back()) != 1)// 移进
		{
			if (relationship_table.at(*stack_top).at(input.back()) == 0)
				cout << setw(24) << left << "=";
			else
				cout << setw(24) << left << "<";
			cout << setw(24) << left << "移进";

			char_stack.push_back(input.back());
			input.pop_back();
		}
		else// 规约
		{
			cout << setw(24) << left << ">";
			cout << setw(24) << left << "规约";
			// 获得最左素短语的位置
			const auto it = FindLeftmostPrimePhrase(char_stack, relationship_table);
			// 提取最左素短语
			auto leftmost_prime_phrase = char_stack.substr(it - char_stack.begin());
//			reverse(leftmost_prime_phrase.begin(), leftmost_prime_phrase.end());
			cout << leftmost_prime_phrase;
			char_stack.erase(it, char_stack.end());
			char_stack.push_back('N');
			// 构建语法树节点
			TreeNode* root = new TreeNode('N');
			for (auto ch : leftmost_prime_phrase)// 对于最左素短语的每一个字符
			{
				if (ch != 'N')
				{
					TreeNode* cur = new TreeNode(ch);
					root->children.push_back(cur);
				}
				else
				{
					root->children.push_back(nodes.back());
					nodes.pop_back();
				}
			}
			nodes.push_back(root);
		}
		cout << endl;
	}
	if (char_stack != "#N#")
		error("规约失败");
	return nodes.back();
}

void PrintNode(TreeNode* node, int depth)
{
	static map<int, bool> rec;
	//	rec[0] = true;
	for (int i = 0; i < depth; i++)
		if (i == depth - 1)
			cout << "└—";
		else
			rec[i + 1] ? cout << "   " : cout << "│  ";
	cout << node->value << endl;
	if (node->children.size() == 0)
		return;

	for (auto child : node->children)
	{
		if (child == node->children.back())
			rec[depth + 1] = true;
		PrintNode(child, depth + 1);
		rec[depth + 1] = false;
	}
}

int main()
{
	vector<gramma_pair_t> gramma;
	cout << "请输入文法，以一行#结束" << endl;
	GetInput(gramma);

	const vt_set_t first_vt = FindVT(gramma, FIRSTVT);
	const vt_set_t last_vt = FindVT(gramma, LASTVT);
	PrintVT(first_vt, last_vt);

	const auto relationship_table = GetRelationshipTable(gramma, first_vt, last_vt);
	PrintRelationshipTable(relationship_table);

	string input;
	cout << "请输入单词串" << endl;
	cin >> input;
	TreeNode* nodes = Analyze(input, relationship_table);

	cout << endl << "========语法分析树=======" << endl;
	PrintNode(nodes, 0);
	system("pause");
	return 0;
}
