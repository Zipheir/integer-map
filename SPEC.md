# Integer Mappings

This library defines integer mappings, which are structures that
define a set of associations between exact integers and arbitrary
Scheme objects.

This library's interface is inspired by SRFI 146 and by Haskell's
IntMap library.

Many functions make use of Maybe values.  See SRFI 189 for details
on this type.

This is a preliminary specification.  It is vague and subject to
change.

# Constructors

`(imapping arg ...)`

Returns a new imapping.  The args alternate between keys (which
must be exact integers) and values (which may be anything); the
resulting imapping contains these (key, value) associations.
The number of args must be even.  If duplicate keys occur in
args, earlier associations take priority.

`(imapping-unfold stop? mapper successor seed)`

Unfold a new imapping.  `mapper` is applied to each seed and returns
two values, a key and an associated value.

`(imapping-unfold-maybe proc seed)`

Unfold a new imapping.  `proc` is applied to each seed and returns
a Maybe value.  If this value is Nothing, then unfolding terminates.
If it is a Just of three values *k, v, seed′*, then a new association
(*k*, *v*) is added to the resulting imapping and unfolding continues
with *seed′*.

The following equivalence between the two imapping-unfold procedures
may clarify things:

    (imapping-unfold p f g x)
      ≡
    (imapping-unfold-maybe (λ (s)
                             (if (p s)
                                 (nothing)
                                 (let-values (((k v) (f s)))
                                   (just k v (g s)))))
                           x)

`(alist->imapping alist)`

Returns a new imapping containing the associations of *alist*.

# Predicates

`(imapping? obj)`

`* → boolean`

Returns `#t` iff *obj* is an imapping.

`(imapping-contains? imap n)`

`imapping int → boolean`

Returns `#t` iff *imap* contains an association for key *n*.

`(imapping-empty? imap)`

`imapping → boolean`

Returns `#t` iff *imap* contains no associations.

`(imapping-disjoint? imap1 imap2)`

`imapping imapping → boolean`

Returns `#t` iff *imap1* and *imap* have no keys in common.

# Accessors

`(imapping-lookup imap n)`

`imapping int → maybe[*]`

If an association *(n, v)* occurs in *imap*, returns Just *v*.
Otherwise, returns Nothing.

`(imapping-lookup-default imap n obj)`

`imapping int * → *`

If an association *(n, v)* occurs in *imap*, returns Just *v*.
Otherwise, returns *obj*.

`(imapping-min imap)`

`imapping → maybe[*]`

Returns Just *n* *v*, where *n* is the least key of *imap*.
If *imap* is empty in the sense of `imapping-empty?`, returns
Nothing.

`(imapping-max imap)`

`imapping → maybe[*]`

Returns Just *n* *v*, where *n* is the greatest key of *imap*.
If *imap* is empty in the sense of `imapping-empty?`, returns
Nothing.

# Updaters

`(imapping-adjoin imap n1 v1 n2 ...)`

`imapping int * int ... → imapping`

Returns a new imapping containing all of the associations of
*imap* as well as the associations *(n1, v1)*, *(n2, v2)*, ...
The number of key/value arguments must be even.

If any of the *ni* already have associations in *imap*, they are
replaced.

`(imapping-adjoin/combine imap proc n1 v1 n2 ...)`

`imapping (* * → *) int * int ... → imapping`

Similar to `imapping-adjoin`, except that duplicate associations
are combined with *proc*.  This procedure is called on the new and
old values (in that order) associated with a duplicated key and is
expected to return a value for the key.

`(imapping-adjust imap n proc)`

`imapping int (* → *) → imapping`

`(imapping-adjust/key imap n proc)`

`imapping int (int * → *) → imapping`

Returns a new imapping in which the association *(n, v)* in *imap*
is replaced by *(n, (proc v))*, or by *(n, (proc n v))* in the
case of `imapping-adjust/key`.  If *n* has no association in *imap*,
then (a copy of) *imap* is returned.
