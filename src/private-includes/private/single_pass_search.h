// Copyright 2008 Jim Xochellis.
// Distributed under the Boost Software License, Version 1.0.

// Boost Software License - Version 1.0 - August 17th, 2003
// (See accompanying file BOOST_LICENSE_1_0.txt or copy at
//  https://www.boost.org/LICENSE_1_0.txt)

// The code of this file has been based on the following paper:

// David R. Musser and Gor V. Nishanov, "A Fast Generic Sequence Matching
// Algorithm," Rensselaer Polytechnic Institute Computer Science Technical
// Report 97-11 (without appendices, 1997); full version available at:
// http://www.cs.rpi.edu/~musser/gp/gensearch1.pdf (revised Feb. 2, 2001).

// Additional modifications have been applied by Jim Xochellis to allow the code
// to work seamlessly with single-pass iterators as input.

// Additional modifications to the code have been applied by Matt Rudary to
// remove deprecated constructs and otherwise modernize the code.

#ifndef __SINGLE_PASS_SEARCH_H__
#define __SINGLE_PASS_SEARCH_H__

#include <algorithm>
#include <functional>
#include <iterator>
#include <vector>

#ifndef USE_BOOST_RANGE
#define USE_BOOST_RANGE 0
#endif

#if USE_BOOST_RANGE

//#include <boost/range.hpp> //too much?
#include <boost/range/functions.hpp>
#include <boost/range/metafunctions.hpp>

#endif

namespace dpx {

template <std::forward_iterator ForwardIterator, typename Distance,
          typename BinaryPredicate>
bool compute_next(ForwardIterator pattern, ForwardIterator patternEnd,
                  std::vector<Distance>& shift,
                  std::vector<ForwardIterator>& pattern_iterator,
                  BinaryPredicate pred) {
  Distance borderIdx = -1;
  shift.reserve(32);
  pattern_iterator.reserve(32);
  shift.push_back(-1);
  pattern_iterator.push_back(pattern);

  bool borderExists = false;

  for (;;) {
    ForwardIterator advance = pattern;
    ++advance;

    if (advance == patternEnd) break;

    // If current tagged-border no longer valid, shift-back to the next best
    // border, similarly to the mismatch/recover procedure of the main
    // algorithm.
    while ((borderIdx >= 0) && !pred(*pattern, *pattern_iterator[borderIdx]))
      borderIdx = shift[borderIdx];

    ++pattern;
    ++borderIdx;

    // Recovering to a position which contains the same value will cause an
    // immediate and unnecessary mismatch, hense we shift-back to the next best
    // border.
    if (pred(*pattern, *pattern_iterator[borderIdx]))
      shift.push_back(shift[borderIdx]);
    else
      shift.push_back(borderIdx);

    if (!borderExists) borderExists = shift.back() > 0;

    pattern_iterator.push_back(pattern);
  }

  return borderExists;
}

//------------------------------------------

/*!

\brief Search for a pattern sequence in a search-range of iterators.

\param[in] searchRange
An input iterator, which points at the first element of the search-range.

\param[in] searchRangeEnd
An input iterator, which denotes the end of the search-range.

\param[in] pattern
A forward iterator, which points at the first element of the pattern sequence.

\param[in] patternEnd
A forward iterator, which points beyond the end of the pattern sequence.

\param[in] pred
A binary predicate, which will used instead of the operator== whenever an
equality test between two elements is performed.

\return
On success the return value is an input iterator which points to the last
element of the first sub-sequence of the search-range that satisfies the search
criteria. On failure the return value is searchRangeEnd.

Searches for a sub-sequence within the search-range [searchRange,
searchRangeEnd), which is identical to the pattern sequence [pattern,
patternEnd), when compared element-by-element through the user defined predicate
pred. Immediately after locating the first sub-sequence that matches these
criteria, it returns an iterator pointing to the last element of the particular
sub-sequence, otherwise it returns searchRangeEnd when the search-range is
exhausted.

*/

template <std::input_iterator InputIterator,
          std::forward_iterator ForwardIterator, typename BinaryPredicate>
InputIterator single_pass_search(InputIterator searchRange,
                                 InputIterator searchRangeEnd,
                                 ForwardIterator pattern,
                                 ForwardIterator patternEnd,
                                 BinaryPredicate pred) {
  // Test for empty ranges
  if ((pattern == patternEnd) || (searchRange == searchRangeEnd))
    return searchRange;  // Success?

  // Test for a pattern of length 1.
  ForwardIterator p1 = pattern;
  ++p1;
  if (p1 == patternEnd)
    return std::find_if(searchRange, searchRangeEnd,
                        [&](auto const& elem) { return pred(elem, *pattern); });

  typedef
      typename std::iterator_traits<ForwardIterator>::difference_type Distance2;
  auto binder2ndPred = [&](auto const& elem) { return pred(elem, *pattern); };

  std::vector<Distance2> shift;
  std::vector<ForwardIterator> pattern_iterator;

  ForwardIterator p;

  if (compute_next(pattern, patternEnd, shift, pattern_iterator, pred)) {
    Distance2 j;

    while (searchRange != searchRangeEnd) {
      // Scan the search-range for a possible match, use std::find
      // to take advantage of optimized specializations

      searchRange = std::find_if(searchRange, searchRangeEnd, binder2ndPred);
      if (searchRange == searchRangeEnd) return searchRangeEnd;  // failure

      // search-range must contain more than just one element
      if (++searchRange == searchRangeEnd) return searchRangeEnd;  // failure

      p = p1;
      j = 1;

      for (;;) {
        while (pred(*searchRange, *p)) {
          if (++p == patternEnd) return searchRange;  // success

          if (++searchRange == searchRangeEnd)
            return searchRangeEnd;  // failure
          ++j;
        }

        // Recover from a mismatch using the shift table

        j = shift[j];

        if (j < 0)  // No border and (*text == *pattern), abort and move
        {           // to the next element of the search-range.
          ++searchRange;
          break;
        }

        if (j == 0)  // No border to shift, restart from
          break;     // first pattern element

        p = pattern_iterator[j];
      }
    }
  } else {
    // No backtracking required because no border exists

    while (searchRange != searchRangeEnd) {
      // Scan the search-range for a possible match, use std::find
      // to take advantage of optimized specializations

      searchRange = std::find_if(searchRange, searchRangeEnd, binder2ndPred);

      if (searchRange == searchRangeEnd) return searchRangeEnd;  // failure

      // search-range must contain more than just one element
      if (++searchRange == searchRangeEnd) return searchRangeEnd;  // failure

      p = p1;

      while (pred(*searchRange, *p)) {
        if (++p == patternEnd) return searchRange;  // success

        if (++searchRange == searchRangeEnd) return searchRangeEnd;  // failure
      }
    }
  }

  return searchRangeEnd;  // failure
}

//------------------------------------------

/*!

\brief Search for a pattern sequence in a search-range of iterators.

\param[in] searchRange
An input iterator, which points at the first element of the search-range.

\param[in] searchRangeEnd
An input iterator, which denotes the end of the search-range.

\param[in] pattern
A forward iterator, which points at the first element of the pattern sequence.

\param[in] patternEnd
A forward iterator, which points beyond the end of the pattern sequence.

\return
On success the return value is an input iterator which points to the last
element of the first sub-sequence of the search-range that satisfies the search
criteria. On failure the return value is searchRangeEnd.

Searches for a sub-sequence within the search-range [searchRange,
searchRangeEnd), which is identical to the pattern sequence [pattern,
patternEnd), when compared element-by-element. Immediately after locating the
first sub-sequence that matches these criteria, it returns an iterator pointing
to the last element of the particular sub-sequence, otherwise it returns
searchRangeEnd when the search-range is exhausted.

*/

template <std::input_iterator InputIterator,
          std::forward_iterator ForwardIterator>
inline InputIterator single_pass_search(InputIterator searchRange,
                                        InputIterator searchRangeEnd,
                                        ForwardIterator pattern,
                                        ForwardIterator patternEnd) {
  typedef
      typename std::iterator_traits<ForwardIterator>::value_type element_type;

  return single_pass_search(searchRange, searchRangeEnd, pattern, patternEnd,
                            std::equal_to<element_type>());
}

//------------------------------------------

#if USE_BOOST_RANGE

/*!

\brief Search for a pattern sequence in a search-range of iterators.

\param[in] searchRange
A Boost single-pass range object reference, which defines the search-range.

\param[in] patternRange
A Boost forward range object reference, which defines the pattern sequence.

\return
On success the return value is a Boost single-pass iterator which points to
the last element of the first sub-sequence of the search-range that satisfies
the search criteria. On failure the return value is boost::end(searchRange).

Searches for a sub-sequence within the search-range defined by searchRange,
which is identical to the pattern sequence defined by pattern, when compared
element-by-element. Immediately after locating the first sub-sequence that
matches these criteria, it returns an iterator pointing to the last element of
the particular sub-sequence, otherwise it returns boost::end(searchRange) when
the search-range is exhausted.

*/

template <typename SinglePassRange, typename ForwardRange>
inline typename boost::range_iterator<SinglePassRange>::type single_pass_search(
    SinglePassRange& searchRange, ForwardRange& patternRange) {
  return single_pass_search(boost::begin(searchRange), boost::end(searchRange),
                            boost::begin(patternRange),
                            boost::end(patternRange));
}

//------------------------------------------

/*!

\brief Search for a pattern sequence in a search-range of iterators.

\param[in] searchRange
A Boost single-pass range object reference, which defines the search-range.

\param[in] patternRange
A Boost forward range object reference, which defines the pattern sequence.

\param[in] pred
A binary predicate, which will used instead of the operator== whenever an
equality test between two elements is performed.

\return
On success the return value is a Boost single-pass iterator which points to
the last element of the first sub-sequence of the search-range that satisfies
the search criteria. On failure the return value is boost::end(searchRange).

Searches for a sub-sequence within the search-range defined by searchRange,
which is identical to the pattern sequence defined by pattern, when compared
element-by-element through the user defined predicate pred. Immediately after
locating the first sub-sequence that matches these criteria, it returns an
iterator pointing to the last element of the particular sub-sequence, otherwise
it returns boost::end(searchRange) when the search-range is exhausted.

*/

template <typename SinglePassRange, typename ForwardRange,
          typename BinaryPredicate>
inline typename boost::range_iterator<SinglePassRange>::type single_pass_search(
    SinglePassRange& searchRange, ForwardRange& patternRange,
    BinaryPredicate pred) {
  return single_pass_search(boost::begin(searchRange), boost::end(searchRange),
                            boost::begin(patternRange),
                            boost::end(patternRange), pred);
}

#endif

}  // namespace dpx

#endif  //__SINGLE_PASS_SEARCH_H__
