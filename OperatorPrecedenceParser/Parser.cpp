/* 1552212 ������ ��Ϣ��ȫ */
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
 * \brief �ж��Ƿ����ս��
 * \param ch 
 * \return true:�ս�� false:���ս��
 */
inline bool TerminalSymbolQ(const char ch)
{
	if (!isupper(ch))
		return true;
	return false;
}

/**
 * \brief ��ȡ�������gramma��
 * \param gramma �ķ�
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
			error("�������!");
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
					error("������ķ�!");
				gramma_item.push_back(v);
			}
			gramma_items.push_back(gramma_item);
		}
		gramma_pair.second = gramma_items;
		gramma.push_back(gramma_pair);
	}
}

/**
 * \brief ����FIRSTVT��LASTVT
 * \param gramma �ķ�
 * \param order ��FIRSTVT����LASTVT
 * \return 
 */
vt_set_t FindVT(vector<gramma_pair_t> gramma, const bool order)
{
	vt_set_t vt_set;
	map<char, map<char, bool>> Fmatrix;
	stack<pair<char, char>> pair_stack;
	for (auto gramma_pair : gramma)// �����ķ���ÿһ��
		for (auto str : gramma_pair.second)// ����ÿһ������ʽ
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
 * \brief ������ȼ���
 * \param gramma �ķ�
 * \param first_vt FIRST��
 * \param last_vt LAST��
 * \return ���ȼ���
 */
map<char, map<char, int>> GetRelationshipTable(const vector<gramma_pair_t>& gramma, const vt_set_t& first_vt,
                                               const vt_set_t& last_vt)
{
	set<char> all_vt;
	map<char, map<char, int>> relationship_table;
	for (auto gramma_pair : gramma)// �����ķ���ÿһ��
		for (gramma_item_t str : gramma_pair.second)// ����ÿһ������ʽ
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
				//  IF  Xi��Xi+1��Ϊ�ս��  THEN  ��Xi = Xi+1
				if (TerminalSymbolQ(*it) && TerminalSymbolQ(*(it + 1)))
				{
					if (relationship_table.find(*it) != relationship_table.end() &&
						relationship_table[*it].find(*(it + 1)) != relationship_table[*it].end())
						error("����������ķ���");
					relationship_table[*it][*(it + 1)] = 0;
				}
				//  IF  i<n-2��Xi��Xi+2��Ϊ�ս��
				// ��Xi + 1Ϊ���ս��  THEN  ��Xi = Xi + 2��
				if (str.size() >= 3 && it <= str.end() - 3 && TerminalSymbolQ(*it) && !TerminalSymbolQ(
					*(it + 1)) && TerminalSymbolQ(*(it + 2)))
				{
					if (relationship_table.find(*it) != relationship_table.end() &&
						relationship_table[*it].find(*(it + 2)) != relationship_table[*it].end())
						error("����������ķ���");
					relationship_table[*it][*(it + 2)] = 0;
				}
				// IF  XiΪ�ս����Xi+1Ϊ���ս��  THEN
				// FOR  FIRSTVT(Xi + 1)�е�ÿ��a  DO
				// �� Xi < a��
				if (TerminalSymbolQ(*it) && !TerminalSymbolQ(*(it + 1)))
					for (auto a : first_vt.at(*(it + 1)))
					{
						if (relationship_table.find(*it) != relationship_table.end() &&
							relationship_table[*it].find(a) != relationship_table[*it].end())
							error("����������ķ���");
						relationship_table[*it][a] = -1;
					}
				// IF  XiΪ���ս����Xi+1Ϊ�ս��  THEN
				// FOR  LASTVT(Xi)�е�ÿ��a   DO
				// ��  a > Xi + 1
				if (!TerminalSymbolQ(*it) && TerminalSymbolQ(*(it + 1)))
					for (auto a : last_vt.at(*it))
					{
						if (relationship_table.find(a) != relationship_table.end() &&
							relationship_table[a].find(*(it + 1)) != relationship_table[a].end())
							error("����������ķ���");
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
 * \brief ���������ض���
 * \param cs �����ַ���
 * \param relationship_table ��ϵ��
 * \return �����ض�����ʼ��iterator
 */
string::const_iterator FindLeftmostPrimePhrase(const string& cs, map<char, map<char, int>> relationship_table)
{
	// cs�ǵ�������
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
 * \brief ��ӡ��ϵ��
 * \param relationship_table 
 */
void PrintRelationshipTable(const map<char, map<char, int>>& relationship_table)
{
	cout << endl << "========���ȹ�ϵ��=======" << endl;

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
 * \brief ��ӡfirst����last��
 * \param first_vt 
 * \param last_vt 
 */
void PrintVT(const vt_set_t& first_vt, const vt_set_t& last_vt)
{
	cout << endl << "========FIRST��=======" << endl;

	for (auto value : first_vt)
	{
		cout << "FIRSTVT(" << value.first << ") = { ";
		for (auto second : value.second)
			cout << second << "  ";
		cout << '}' << endl;
	}
	cout << "========LAST��========" << endl;
	for (auto value : last_vt)
	{
		cout << "LASTVT(" << value.first << ") = { ";
		for (auto second : value.second)
			cout << second << "  ";
		cout << '}' << endl;
	}
}


/**
 * \brief �������봮
 * \param input �����ַ���
 * \param relationship_table ��ϵ��
 * \return �﷨������
 */
TreeNode* Analyze(string input, const map<char, map<char, int>>& relationship_table)
{
	vector<TreeNode*> nodes;
	string char_stack;

	cout << endl << "����ջ\t\t\t���봮\t\t\t��ϵ\t\t\t����\t\t\t�����ض���" << endl;
	// ����Ҫ��input��Ϊջ��������Ҫ����
	reverse(input.begin(), input.end());
	char_stack.push_back('#');
	while (!input.empty())
	{
		cout << setw(24) << left << char_stack;
		// input�ǵ��õģ����ʱ��Ҫ��תһ��
		reverse(input.begin(), input.end());
		cout << setw(24) << left << input;
		reverse(input.begin(), input.end());
		// char_stack�ǵ��õģ�endΪջ��
		auto stack_top = char_stack.end();
		while (!TerminalSymbolQ(*--stack_top));

		if (relationship_table.at(*stack_top).find(input.back()) == relationship_table.at(*stack_top).end())
			error("���ķ��ķ��Ż������ȼ�");
		else if (relationship_table.at(*stack_top).at(input.back()) != 1)// �ƽ�
		{
			if (relationship_table.at(*stack_top).at(input.back()) == 0)
				cout << setw(24) << left << "=";
			else
				cout << setw(24) << left << "<";
			cout << setw(24) << left << "�ƽ�";

			char_stack.push_back(input.back());
			input.pop_back();
		}
		else// ��Լ
		{
			cout << setw(24) << left << ">";
			cout << setw(24) << left << "��Լ";
			// ��������ض����λ��
			const auto it = FindLeftmostPrimePhrase(char_stack, relationship_table);
			// ��ȡ�����ض���
			auto leftmost_prime_phrase = char_stack.substr(it - char_stack.begin());
//			reverse(leftmost_prime_phrase.begin(), leftmost_prime_phrase.end());
			cout << leftmost_prime_phrase;
			char_stack.erase(it, char_stack.end());
			char_stack.push_back('N');
			// �����﷨���ڵ�
			TreeNode* root = new TreeNode('N');
			for (auto ch : leftmost_prime_phrase)// ���������ض����ÿһ���ַ�
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
		error("��Լʧ��");
	return nodes.back();
}

void PrintNode(TreeNode* node, int depth)
{
	static map<int, bool> rec;
	//	rec[0] = true;
	for (int i = 0; i < depth; i++)
		if (i == depth - 1)
			cout << "����";
		else
			rec[i + 1] ? cout << "   " : cout << "��  ";
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
	cout << "�������ķ�����һ��#����" << endl;
	GetInput(gramma);

	const vt_set_t first_vt = FindVT(gramma, FIRSTVT);
	const vt_set_t last_vt = FindVT(gramma, LASTVT);
	PrintVT(first_vt, last_vt);

	const auto relationship_table = GetRelationshipTable(gramma, first_vt, last_vt);
	PrintRelationshipTable(relationship_table);

	string input;
	cout << "�����뵥�ʴ�" << endl;
	cin >> input;
	TreeNode* nodes = Analyze(input, relationship_table);

	cout << endl << "========�﷨������=======" << endl;
	PrintNode(nodes, 0);
	system("pause");
	return 0;
}
