/* Copyright (C) 2017, 2021-2026 Hans Åberg.

   This file is part of MLI, MetaLogic Inference.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */


#include <bit>
#include <exception>
#include <iterator>
#include <sstream>
#include <iomanip>
#include <string>
#include <tuple>


namespace utf {

  using uint = unsigned;

  // Powers of 2, k <= 63
  inline uint64_t pow2(uint8_t k) { return ((uint64_t)1) << k; }


  // Write x in hexadecimal form, with leading string c"x":
  inline std::string to_hex(uint32_t x, char c = '\\')
  {
    std::ostringstream r;
    r << c << "x" << std::setw(2) << std::setfill('0') << std::hex << std::uppercase << x;

    return r.str();
  }


  // Length of string in bytes after converting to UTF-8.
  // Extends UTF-8 by setting length of x > 0x7FFFFFFF to 6, thus
  // admitting 6 byte regular expressions for these numbers.
  inline size_t length_utf8(char32_t x)
  {
    if (x <= 0x0000007F) return 1;
    if (x <= 0x000007FF) return 2;
    if (x <= 0x0000FFFF) return 3;
    if (x <= 0x001FFFFF) return 4;
    if (x <= 0x03FFFFFF) return 5;
    // The following line makes x > 0x7FFFFFFF admissable, as 6 byte sequences:
    return 6;
  }


  // Length of string in bytes after converting to UTF-8.
  inline size_t length_utf8(const std::u32string& x)
  {
    size_t n = 0;

    for (auto& i: x)
      n += length_utf8(i);

    return n;
  }


  // Converting a Unicode code point value to a UTF-8 string, extended to
  // all char32_t values, up to 6 bytes.
  // Eventual checks for exceeding Unicode maximum value 0x0010ffffu must be done
  // separately.

  // The length l is the number of bytes in the found sequence, and the size s is
  // the number of bytes indicated in the leading byte.
  // Thus l ≤ s, and possible values are 1, …, 6.
  // In case of a valid sequence, l = s = 0.
  // If the sequence is a spurious trailing byte 10xxxxxx, l = s = 1.
  // For an overlong or truncated sequence:
  // For an overlong sequence, l = s ∈ [2, 6].
  // For a truncated sequence, 1 ≤ l < s ≤ 6.
  // The valid data bits in the found sequence:
  //    s  Leading byte
  //    2  110xxxxx
  //    3  1110xxxx
  //    4  11110xxx
  //    5  111110xx
  //    6  111111xx
  // Followed by l - 1 trailing bytes 10xxxxxx.
  // Total number of bits (7 - s) + (s == 6) + 6(l - 1)

  // Valid argument values:
  // l = s = 0: k any char32_t value
  // l = s = 1: k ∈ [0, 0x3f]
  // l = s ∈ [2, 6]: b = 5*l + 1 + (l == 6), though overlong if k ∈ [0, 2^b - 1], where b = 5*l + 1 + (l == 6)
  // s ∈ [2, 6], l ∈ [1, s - 1]: k bits b (7 - s + (s == 6)) + 6(l - 1), k ∈ [0, 2^b - 1]

  inline std::string to_utf8(char32_t k, uint8_t l, uint8_t s)
  {

    if (l > 6)
      throw std::domain_error(
       "Second argument must be <= 6 in to_utf8("
        + to_hex(k) + ", " + std::to_string((uint)l) + ", " + std::to_string((uint)s) + ").");

    if (s > 6)
      throw std::domain_error(
       "Third argument must be <= 6 in to_utf8("
        + to_hex(k) + ", " + std::to_string((uint)l) + ", " + std::to_string((uint)s) + ").");

    if (s <= 1 && l != s)
      throw std::domain_error(
       "Second argument must equal to third when the latter is <= 1 (valid or spurious sequences) in to_utf8("
        + to_hex(k) + ", " + std::to_string((uint)l) + ", " + std::to_string((uint)s) + ").");

    // Spurious
    if (l == 1 && s == 1 && k >= 0x40)
      throw std::domain_error(
       "First argument must be < 0x40, spurious trailing byte value 10xxxxxx, in to_utf8("
        + to_hex(k) + ", " + std::to_string((uint)l) + ", " + std::to_string((uint)s) + ").");

    // Overlong
    if (s >= 2 && l == s) {
      if (k >= pow2(5*l + 1))
        throw std::domain_error(
         "First argument must be <= " + to_hex(pow2(5*l + 1) - 1) + " in to_utf8("
          + to_hex(k) + ", " + std::to_string((uint)l) + ", " + std::to_string((uint)s) + ").");
    }

    // Truncated
    if (s >= 2 && l != s) {
      if (l < 1)
        throw std::domain_error(
         "Second argument must be >= 1 in to_utf8("
          + to_hex(k) + ", " + std::to_string((uint)l) + ", " + std::to_string((uint)s) + ").");

      size_t n = (7 - s + (s == 6)) + 6*(l - 1); // Number of bits.

      if (k >= pow2(n))
        throw std::domain_error(
         "First argument must be <= " + to_hex(pow2(n) - 1) + " in to_utf8("
          + to_hex(k) + ", " + std::to_string((uint)l) + ", " + std::to_string((uint)s) + ").");
    }

    // Number of bytes in the sequence:
    size_t m = (s == 0)? length_utf8(k) : l;

    // Size indicated in leading byte:
    size_t n = (s == 0)? m : ((s == 1)? 0 : s);

    std::string r(m, '\0'); // String of n bytes.

    // Builds the UTF-8 string starting with the last, least significant byte (octet):

    for (size_t i = m - 1; i > 0; --i) {
      r[i] = k & 0x3f | 0x80;
      k >>= 6;
    }

    switch (n) {
      case 0: r[0] = k | 0x80; break;   // Spurious trailing byte
      case 1: r[0] = k; break;
      case 2: r[0] = k | 0xc0; break;
      case 3: r[0] = k | 0xe0; break;
      case 4: r[0] = k | 0xf0; break;
      case 5: r[0] = k | 0xf8; break;
      case 6: r[0] = k | 0xfc; break;
    }

    return r;
  }


  inline std::string to_string(char32_t k)
  {
    size_t n = length_utf8(k);

    std::string r(n, '\0'); // String of n bytes.

    // Builds the UTF-8 string starting with the last, least significant byte (octet):

    for (size_t i = n - 1; i > 0; --i) {
      r[i] = k & 0x3f | 0x80;
      k >>= 6;
    }

    switch (n) {
      case 1: r[0] = k; break;
      case 2: r[0] = k | 0xc0; break;
      case 3: r[0] = k | 0xe0; break;
      case 4: r[0] = k | 0xf0; break;
      case 5: r[0] = k | 0xf8; break;
      case 6: r[0] = k | 0xfc; break;
    }

    return r;
  }


  // Convert a u32string to a UTF-8 string. Does not throw exceptions.
  inline std::string to_string(const std::u32string& x)
  {
    // Make a single allocation:
    size_t n = length_utf8(x);
    std::string s(n, '\0');

    size_t j = 0; // Position in s.

    for (auto& i: x) {
      std::string s0 = to_string(i);
      size_t n0 = s0.size();
      s.replace(j, n0, s0);
      j += n0;
    }

    return s;
  }


  inline std::u8string to_u8string(char32_t k) {
    std::string s = to_string(k);

    return {s.begin(), s.end()};
  }


  // Convert a u32string to a u8string. Does not throw exceptions.
  inline std::u8string to_u8string(const std::u32string& x)
  {
    std::string s = to_string(x);

    return {s.begin(), s.end()};
  }


  // Number of valid UTF-8 characters in the semiopen interval [it, it1), with the
  // invalid byte sequences counted so that it determines the number of UTF-32 characters
  // with errors replaced by � REPLACEMENT CHARACTER U+FFFD.
  template<class Iterator>
  inline std::size_t length_utf8(Iterator it, Iterator it1)
  {
    std::size_t r = 0;

    while (it != it1) {
      uint8_t a0 = *it;

      // If highest bit is 0, it is in the ASCII range
      // If it 1 and the next highest bit is 0, it is not a leading byte.
      // So in both cases, continue.
      if (!(a0 & 0x80) || !(a0 & 0x40)) {
        ++r;
        ++it;
        continue;
      }

      // The leading byte is now of the form 11xxxxxx.

      // Length of UTF-8 byte sequence as indicated by leading byte:
      // Find number of highest 1 bits in leading byte, at most 6 bits, as the
      // two last bits are used for the return value, extending UTF-8 to
      // allow for a full 32-bit number to be stored in a maximum of 6 bytes.

      size_t n = 0; // Length of UTF-8 byte sequence as indicated by leading byte.

      for (uint8_t k = 0x80; (a0 & k) != 0 && k != 0x02; k >>= 1, ++n)
        ;

      size_t k = 1; // Length of trailing UTF-8 byte sequence plus one.

      // Read at most n - 1 bytes and that are of the form 10xxxxxx.
      // If a lower number of bytes are read, then the sequence is invalid
      // but is replaced by a single value in the conversion to UTF-32.
      for (++it; k < n && (*it & 0xC0) == 0x80; ++it, ++k)
        ;

      ++r;
    }

    return r;
  }


  // Number of valid and invalid UTF-8 sequences in a byte string.
  // A byte sequences is scanned until either it is complete or an invalid byte
  // found, which is then included in the sequence.
  // It is the number of UTF-32 characters if invalid byte sequences are
  // replaced by � REPLACEMENT CHARACTER U+FFFD.
  inline std::size_t length_utf8(const std::string& s)
  {
    return length_utf8(s.begin(), s.end());
  }


  // From a UTF-8 input iterator, read a single UTF-32 character into char32_t.
  template<class Iterator>
  inline Iterator get(Iterator it, Iterator it1, char32_t& c, uint8_t& l, uint8_t& s)
  {
    if (it == it1)
      return it;

    uint8_t a0 = *it++;

    // Count the number of leading 1 bits:
    //   0  ASCII range
    //   1  UTF-8 trailing byte
    // Otherwise, the number of bytes in full UTF-8 sequence, up to maximum 6.
    size_t n = std::min(std::countl_one(a0), 6);

    // ASCII range no leading 1s; continue for next byte.
    if (n == 0) {
      c = a0;
      l = s = 0;
      return it;
    }

    // Spurious trailing byte if exactly one leading 1:
    if (n == 1) {
      // Zero the leading 1 of a0 = 10xxxxxx.
      c = a0 & 0x3f; //
      l = s = 1;
      return it;
    }

    // The leading byte is now of the form 11xxxxxx.

    // Zero out n <= 6 highest 1 bits in leading byte, at most 6 bits as the
    // two last bits are used for the return value, extending UTF-8 to
    // allow for a full 32-bit number to be stored in a maximum of 6 bytes.
    a0 <<= n; // Shift out n <= 6 highest 1 bits.
    a0 >>= n; // Shift down n <= 6 highest 0 bits.

    char32_t a = a0;  // Return value.

    size_t k = 1;     // Length of trailing UTF-8 byte sequence plus one.
    bool q0 = true;   // True on first iteration, then false.
    uint8_t a1 = 0;   // First trailing byte.

    // Add values for trailing bytes as leading byte value already in a.
    // Read at most n - 1 bytes, and that are of the form 10xxxxxx.
    for (; it != it1 && k < n && (*it & 0xC0) == 0x80; ++k) {
      uint8_t b = *it++;

      if (q0) {
        a1 = b & 0x3f; // Record data of first trailing byte for overlong check.
        q0 = false;
      }

      a <<= 6;
      a += b & 0x3f;
    }


    // Check for correct trailing byte length. If a trailing byte was
    // found that is not of the form 10xxxxxx, then k < n.
    if (k < n) {
      c = a;
      l = k;
      s = n;
      return it;
    }


    // The UTF-8 byte sequence now has correct length, but may be overlong.
    //
    // A length 2 byte sequence is overlong if of the form 1100000x 10xxxxxx;
    // enough to check the leading byte.
    // A byte sequence of length n > 2 is overlong if the leading byte data value
    // is 0 (leading bits set to 0), and the first trailng byte with leading 1
    // set to 0 has n high 0 bits.
    bool ol = false; // Set to true if overlong.

    if (n == 2)
      ol = (a0 & 0xde) == 0x00;
    else if (a0 == 0)
      switch (n) {
        case 3: ol = (a1 & 0x20) == 0x00; break;
        case 4: ol = (a1 & 0x30) == 0x00; break;
        case 5: ol = (a1 & 0x38) == 0x00; break;
        case 6: ol = (a1 & 0x3c) == 0x00; break;
      }

    if (ol) {
      c = a;
      l = s = n;
      return it;
    }

    c = a;
    l = s = 0;

    return it;
  }


  // From a UTF-8 input iterator, read a single UTF-32 char32_t character, and return the
  // result, along with the iterator after the read sequence.
  template<class Iterator>
  inline std::pair<std::tuple<char32_t, uint8_t, uint8_t>, Iterator> to_char32_t(Iterator it, Iterator it1)
  {
    char32_t c = std::char_traits<char32_t>::eof();
    uint8_t l = 0, s = 0;

    Iterator it2 = get(it, it1, c, l, s);

    return {{c, l, s}, it2};
  }


  class utf32_error : public std::domain_error {
    std::tuple<char32_t, uint8_t, uint8_t> data_;
  public:
    utf32_error(const std::string& s, const std::tuple<char32_t, uint8_t, uint8_t>& d)
     : std::domain_error(s), data_(d) {}

    std::tuple<char32_t, uint8_t, uint8_t> data() const { return data_; }

  };


  // Maximum value byte sequences for each byte/bit length.
  // Byte length, bit length, maximum value for bit length:
  //  1   7  \x7f
  //  2  11  \xdf\xbf
  //  3  16  \xef\xbf\xbf
  //  4  21  \xf7\xbf\xbf\xbf
  //  5  26  \xfb\xbf\xbf\xbf\xbf
  //  6  31  \xfd\xbf\xbf\xbf\xbf\xbf
  //  6  32  \xff\xbf\xbf\xbf\xbf\xbf

  // Converting a UTF-8 string to a u32string.
  // Invalid UTF-8 sequences are replaced by:
  //   � REPLACEMENT CHARACTER U+FFFD, UTF-8 EF BF BD.
  // Types of errors, as all bytes of the form 0xxxxxxx are valid, only
  // bytes of the form 1xxxxxxx can generate an error:
  // 1. Leading byte not of the form 11xxxxxx.
  // 2. Truncated: Not as many trailing bytes as indicated by the leading byte, that
  //   is, a byte not of the form 10xxxxxx appears before reading all trailing bytes.
  // 3. Overlong: The value can be fit into a shorter byte sequence.

  // Invalid byte sequences throws exception utf32_error. The original byte sequence
  // can be revored by the use of to_utf8(char32_t k, uint8_t l, uint8_t s).
  template<class Iterator>
  std::u32string to_u32string(Iterator it, Iterator it1)
  {
    std::u32string r;

    while (it != it1) {
      auto pt = to_char32_t(it, it1);
      it = pt.second;

      if (std::get<2>(pt.first) == 0)
        r += std::get<0>(pt.first);
      else
        throw utf32_error(
         "Invalid conversion to char32_t, as from to_utf8("
          + to_hex(std::get<0>(pt.first)) + ", " + std::to_string((uint)std::get<1>(pt.first)) + ", " + std::to_string((uint)std::get<1>(pt.first)) + ").", pt.first);

      it = pt.second;
    }

    return r;
  }


  // Replaces invalid sequenced with char32_t err. A recommended value is err = 0xfffd.
  template<class Iterator>
  std::u32string to_u32string(Iterator it, Iterator it1, char32_t err)
  {
    std::u32string r;

    while (it != it1) {
      auto pt = to_char32_t(it, it1);
      it = pt.second;

      if (std::get<2>(pt.first) == 0)
        r += std::get<0>(pt.first);
      else
        r += err; // Invalid byte sequence replaced by U+FFFD.

      it = pt.second;
    }

    return r;
  }


  // Convert to u32string if the string is valid UTF-8, throw exception if not.
  inline std::u32string to_u32string(const std::string& s) {
    return to_u32string(s.begin(), s.end());
  }


  // Convert to u32string, does not throws exceptions if u8string is valid UTF-8.
  inline std::u32string to_u32string(const std::u8string& s) {
    return to_u32string(s.begin(), s.end());
  }


  // Verify that the string is valid UTF-8, throw exception if not.
  inline std::u8string to_u8string(const std::string& x) {
    return to_u8string(to_u32string(x));
  }


  // In case of a valid sequence, l = s = 0.
  // If the sequence is a spurious trailing byte 10xxxxxx, l = s = 1.
  // For an overlong or truncated sequence:
  // The length l is the number of bytes in the found sequence, and the size s is
  // the number of bytes indicated in the leading byte.
  // Thus l ≤ s, and possible values are 1, …, 6.
  // For an overlong sequence, l = s, and for a truncated sequence, l < s.
  template<class Char>
  std::basic_istream<Char>& get(std::basic_istream<Char>& is, char32_t& c, uint8_t& l, uint8_t& s)
  {
    if (!is.good())
      return is;

    std::istreambuf_iterator<Char> it0(is.rdbuf());
    std::istreambuf_iterator<Char> it1;

    auto it = get(it0, it1, c, l, s);

    if (it == std::istreambuf_iterator<Char>())
      is.setstate(std::ios_base::eofbit|std::ios_base::failbit);

    return is;
  }


  template<class Char>
  std::basic_istream<Char>& get(std::basic_istream<Char>& is, char32_t& c)
  {
    if (!is.good())
      return is;

    std::istreambuf_iterator<Char> it0(is.rdbuf());
    std::istreambuf_iterator<Char> it1;

    uint8_t l, s;

    auto it = get(it0, it1, c, l, s);

    if (it == std::istreambuf_iterator<Char>())
      is.setstate(std::ios_base::eofbit|std::ios_base::failbit);

      if (s != 0)
        throw utf32_error(
         "Invalid conversion to char32_t, as from to_utf8("
          + to_hex(c) + ", " + std::to_string((uint)l) + ", " + std::to_string((uint)s) + ").", {c, l, s});


    return is;
  }


  template<class Char>
  std::basic_istream<Char>& getline(std::basic_istream<Char>& is, std::u32string& s, char32_t d = '\n')
  {
    s.erase();

    while (is) {
      char32_t c;

      get<Char>(is, c);

      if (!is.good() || c == d)
        break;

      s += c;
    }

    return is;
  }


  // Class for UTF-32 character strings, with additions not available in std::u32string.
  class u32string : public std::u32string {
  public:
    u32string() = default;

    u32string(const std::string& s) : std::u32string(to_u32string(s.begin(), s.end())) {}
    u32string(const std::string& s, char32_t err) : std::u32string(to_u32string(s.begin(), s.end(), err)) {}

    u32string(const std::u8string& s) : std::u32string(to_u32string(s.begin(), s.end())) {}    u32string(const std::u8string& s, char32_t err) : std::u32string(to_u32string(s.begin(), s.end(), err)) {}

    u32string(size_type k, char c) : u32string(std::string(k, c)) {}
    u32string(const char* cp, size_type k) : u32string(std::string(cp, k)) {}
    u32string(const char* cp) : std::u32string(to_u32string(cp)) {}

    operator std::string() const { return to_string(*this); }
  };


} // namspace utf


namespace std {

  inline std::ostream& operator<<(std::ostream& os, char32_t c)
  {
    os << utf::to_string(c);

    return os;
  }


  inline std::ostream& operator<<(std::ostream& os, const std::u32string& s)
  {
    for (auto& i: s)
      os << i;

    return os;
  }


  inline std::istream& operator>>(std::istream& is, char32_t& c)
  {
    return utf::get(is, c);
  }


  inline std::istream& operator>>(std::istream& is, std::basic_streambuf<char32_t>* sb)
  {
    char32_t c;

    while (is) {
      is >> c;
      sb->sputc(c);
    }

    return is;
  }


  using ou8stream = std::basic_ostream<char8_t>;
  using iu8stream = std::basic_istream<char8_t>;
  using ou8stringstream = std::basic_ostringstream<char8_t>;
  using iu8stringstream = std::basic_istringstream<char8_t>;


  inline std::ou8stream& operator<<(std::ou8stream& os, char32_t c)
  {
    std::u8string s = utf::to_u8string(c);

    for (auto& i: s)
      os.put(i);

    return os;
  }


  inline std::ou8stream& operator<<(std::ou8stream& os, const std::u32string& s)
  {
    for (auto& i: s)
      os << i;

    return os;
  }


  inline std::iu8stream& operator>>(std::iu8stream& is, char32_t& c)
  {
    return utf::get(is, c);
  }


  inline std::iu8stream& operator>>(std::iu8stream& is, std::basic_streambuf<char32_t>* sb)
  {
    char32_t c;

    while (is) {
      is >> c;
      sb->sputc(c);
    }

    return is;
  }



} // namespace std
