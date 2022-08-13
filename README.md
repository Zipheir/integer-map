# integer-map

This is the CHICKEN version of the SRFI 224 Scheme library providing
fixnum (integer) maps.  For the (more) portable version, see the
[SRFI repo](https://github.com/scheme-requests-for-implementation/srfi-224).

Fixnum maps (fxmappings) are implemented using the big-endian
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
