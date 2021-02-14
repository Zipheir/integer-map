# integer-map

This is a Scheme library providing integer maps.  It should be
portable to R7RS Schemes, and may be easily adapted to others.

Integer maps (imappings) are implemented using the big-endian
radix (Patricia) tree structure described by Chris Okasaki and
Andrew Gill in
["Fast Mergeable Integer Maps"](http://ittc.ku.edu/~andygill/papers/IntMap98.pdf).
These provide fast lookup and set-theoretical operations.

# Copying

This is free and open-source software released under the MIT/X
license.  See LICENSE.

# Author

Wolfgang Corcoran-Mathe

wcm at sigwinch dot xyzzy minus the zy
