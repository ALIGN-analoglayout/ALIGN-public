/**
 * @file   String.h
 * @brief  Check string is integer, floating point, number...
 * Convert string to upper/lower cases 
 * @author Yibo Lin
 * @date   Oct 2014
 */

#ifndef _LIMBO_STRING_STRING
#define _LIMBO_STRING_STRING

#include <iostream>
#include <string>
#include <cctype>
#include "ToString.h"

/// @brief namespace for Limbo
namespace limbo 
{ 

using std::cout;
using std::endl;
using std::string;

/// @brief check whether string represents an integer 
/// @param s string 
/// @return true if s is an integer 
inline bool is_integer(string const& s)
{
	if (s.empty()) return false;
	for (string::const_iterator it = s.begin(); it != s.end(); ++it)
	{
		if (!isdigit(*it)) return false;
	}
	return true;
}

/// @brief check whether string represents an float 
/// @param s string 
/// @return true if s is an float 
inline bool is_float(string const& s)
{
	if (s.empty()) return false;
	short dp_cnt = 0; // count how many times the decimal point appears 
					// if it appears more than 1, then s is not a floating point number 
	for (string::const_iterator it = s.begin(); it != s.end(); ++it)
	{
		if (!isdigit(*it))
		{
			if (*it == '.' && dp_cnt < 1) // dp_cnt should be <= 1 
				++dp_cnt;
			else return false;
		}
	}
	// for floating point we assume decimal point should be there 
	return dp_cnt == 1;
}

/// @brief check whether string represents a number, either integer or floating point number 
/// @param s string 
/// @return true if s is a number 
inline bool is_number(string const& s)
{
	if (s.empty()) return false;
	short dp_cnt = 0; // count how many times the decimal point appears 
					// if it appears more than 1, then s is not a floating point number 
	for (string::const_iterator it = s.begin(); it != s.end(); ++it)
	{
		if (!isdigit(*it))
		{
			if (*it == '.' && dp_cnt < 1) // dp_cnt should be <= 1 
				++dp_cnt;
			else return false;
		}
	}
	// no requirement for floating point here 
	return true;
}

/// @brief convert string to upper case 
/// @param s string 
/// @return upper case copy of s 
inline string toupper(string const& s)
{
	string s_up;
	s_up.reserve(s.size());
	for (string::const_iterator it = s.begin(); it != s.end(); ++it)
		s_up.push_back(::toupper(*it));
	return s_up;
}

/// @brief convert string to lower case 
/// @param s string 
/// @return lower case copy of s 
inline string tolower(string const& s)
{
	string s_low;
	s_low.reserve(s.size());
	for (string::const_iterator it = s.begin(); it != s.end(); ++it)
		s_low.push_back(::tolower(*it));
	return s_low;
}

/// @brief check two strings equal, case-insensitive 
/// @param s1 string 
/// @param s2 string 
/// @return true if s1 and s2 are equal case-insensitively 
inline bool iequals(string const& s1, string const& s2)
{
	string s1_up = toupper(s1);
	string s2_up = toupper(s2);
	return s1_up == s2_up;
}

/// @brief get relative path of a file
/// @param s file name 
/// @return the relative path of a file
inline string get_file_path(const string& s)
{
	size_t found = s.rfind('/');
	if (found != string::npos) return s.substr(0, found);
	else return ".";
}
/// @brief get pure name of a file (no path)
/// @param s file name 
/// @return the pure name of a file (no path)
inline string get_file_name(const string& s)
{
	size_t found = s.rfind('/');
	if (found != string::npos) return s.substr(found+1);
	else return s;
}
/// @brief get suffix of a file 
/// @param s file name 
/// @return the suffix of a file 
inline string get_file_suffix(const string& s)
{
	size_t found = s.rfind('.');
	if (found != string::npos) return s.substr(found+1);
	else return string("");
}
/// @brief trim the suffix of a file 
/// @param s file name 
/// @return string without suffix of the file 
inline string trim_file_suffix(string const& s)
{
	size_t found = s.rfind('.');
	if (found != string::npos) return s.substr(0, found);
	else return s;
}
/// @brief fetch the first word of a string, assume delimiter is space or tab
/// @param str string 
/// @return the first word of a string, assume delimiter is space or tab
inline string get_first_word(string const& str)
{
	size_t pos1 = std::string::npos;
	size_t pos2 = std::string::npos;
	for (size_t i = 0; i < str.size(); i++)
	{
		if (pos1 == std::string::npos && str[i] != ' ' && str[i] != '\t')
			pos1 = i;
		else if (pos1 != std::string::npos && (str[i] == ' ' || str[i] == '\t'))
		{
			pos2 = i;
			break;
		}
	}
	return str.substr(pos1, pos2 - pos1);
}

} // namespace limbo 

#endif 
