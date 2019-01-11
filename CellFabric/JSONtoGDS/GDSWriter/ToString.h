/**
 * @file   ToString.h
 * @brief  convert metadata type to string 
 * @author Yibo Lin
 * @date   Apr 2015
 */

#ifndef _LIMBO_STRING_TOSTRING
#define _LIMBO_STRING_TOSTRING

#include <string>
#include <cstdio>
#include <limits>

/// @brief namespace for Limbo
namespace limbo 
{

using std::string;

/// @brief convert integer to string 
/// @param val integer 
/// @return string 
inline string to_string(int val)
{
	char a[sizeof(int)<<2]; 
	sprintf(a, "%d", val);
	return string(a);
}
/// @brief convert long integer to string 
/// @param val long integer 
/// @return string 
inline string to_string(long val)
{
	char a[sizeof(long)<<2]; 
	sprintf(a, "%ld", val);
	return string(a);
}
/// @brief convert long long integer to string 
/// @param val long long integer 
/// @return string 
inline string to_string(long long val)
{
	char a[sizeof(long long)<<2]; 
	sprintf(a, "%lld", val);
	return string(a);
}
/// @brief convert unsigned integer to string 
/// @param val unsigned integer 
/// @return string 
inline string to_string(unsigned int val)
{
	char a[sizeof(unsigned int)<<2]; 
	sprintf(a, "%u", val);
	return string(a);
}
/// @brief convert unsigned long integer to string 
/// @param val unsigned long integer 
/// @return string 
inline string to_string(unsigned long val)
{
	char a[sizeof(unsigned long)<<2]; 
	sprintf(a, "%lu", val);
	return string(a);
}
/// @brief convert unsigned long long integer to string 
/// @param val unsigned long long integer 
/// @return string 
inline string to_string(unsigned long long val)
{
	char a[sizeof(unsigned long long)<<2]; 
	sprintf(a, "%llu", val);
	return string(a);
}
/// @brief convert float to string 
/// @param val float 
/// @return string 
inline string to_string(float val)
{
	if (val != val) return string("nan");
	char a[std::numeric_limits<float>::max_exponent10+20]; 
	sprintf(a, "%g", val);
	return string(a);
}
/// @brief convert double to string 
/// @param val double 
/// @return string 
inline string to_string(double val)
{
	if (val != val) return string("nan");
	char a[std::numeric_limits<double>::max_exponent10+20]; 
	sprintf(a, "%g", val);
	return string(a);
}
/// @brief convert long double to string 
/// @param val long double 
/// @return string 
inline string to_string(long double val)
{
	if (val != val) return string("nan");
	char a[std::numeric_limits<long double>::max_exponent10+20]; 
	sprintf(a, "%Lf", val);
	return string(a);
}

} // namespace limbo 

#endif
