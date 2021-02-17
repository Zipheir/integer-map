# Integer Mappings

This library defines integer mappings, which are structures that
define a set of associations between exact integers and arbitrary
Scheme objects.  The interface is inspired by SRFI 146 and by Haskell's
IntMap library.

Many functions make use of Maybe values.  See SRFI 189 for details
on this type.

This is a preliminary specification.  It is vague and subject to
change.

# Constructors

`(imapping n1 v1 n2 …)`

int \* int … → imapping

Returns a new imapping.  The args alternate between keys (which
must be exact integers) and values (which may be anything); the
resulting imapping contains these (key, value) associations.
The number of args must be even.  If duplicate keys occur in
args, earlier associations take priority.

`(imapping-unfold stop? mapper successor seed)`

Unfold a new imapping.  `mapper` is applied to each seed and returns
two values, a key and an associated value.

`(imapping-unfold-maybe mproc seed)`

(\* → maybe[\* \* \*]) \* → imapping

Unfold a new imapping.  *mproc* is applied to *seed* and returns
a Maybe value.  If this value is Nothing, then unfolding terminates.
If it is a Just of three values *k, v, seed′*, then a new association
*(k, v)* is added to the resulting imapping and unfolding continues
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

list[(int . \*)] → imapping

Returns a new imapping containing the associations of *alist*.

# Predicates

`(imapping? obj)`

\* → boolean

Returns `#t` iff *obj* is an imapping.

`(imapping-contains? imap n)`

imapping int → boolean

Returns `#t` iff *imap* contains an association for key *n*.

`(imapping-empty? imap)`

imapping → boolean

Returns `#t` iff *imap* contains no associations.

`(imapping-disjoint? imap1 imap2)`

imapping imapping → boolean

Returns `#t` iff *imap1* and *imap* have no keys in common.

# Accessors

`(imapping-lookup imap n)`

imapping int → maybe[\*]

If an association *(n, v)* occurs in *imap*, returns Just *v*.
Otherwise, returns Nothing.

`(imapping-lookup-default imap n obj)`

imapping int \* → \*

If an association *(n, v)* occurs in *imap*, returns Just *v*.
Otherwise, returns *obj*.

`(imapping-min imap)`

imapping → maybe[*]

Returns Just *n* *v*, where *n* is the least key of *imap*.
If *imap* is empty in the sense of `imapping-empty?`, returns
Nothing.

`(imapping-max imap)`

imapping → maybe[\*]

Returns Just *n* *v*, where *n* is the greatest key of *imap*.
If *imap* is empty in the sense of `imapping-empty?`, returns
Nothing.

# Updaters

`(imapping-adjoin imap n1 v1 n2 …)`

imapping int \* int … → imapping

Returns a new imapping containing all of the associations of
*imap* as well as the associations *(n1, v1)*, *(n2, v2)*, …
The number of key/value arguments must be even.

If any of the *ni* already have associations in *imap*, they are
replaced.

`(imapping-adjoin/combine imap proc n1 v1 n2 …)`

imapping (\* \* → \*) int \* int … → imapping

Similar to `imapping-adjoin`, except that duplicate associations
are combined with *proc*.  This procedure is called on the new and
old values (in that order) associated with a duplicated key and is
expected to return a value for the key.

`(imapping-adjust imap n proc)`

imapping int (\* → \*) → imapping

`(imapping-adjust/key imap n proc)`

imapping int (int \* → \*) → imapping

Returns a new imapping in which the association *(n, v)* in *imap*
is replaced by *(n, (proc v))*, or by *(n, (proc n v))* in the
case of `imapping-adjust/key`.  If *n* has no association in *imap*,
then (a copy of) *imap* is returned.

`(imapping-delete imap n1 n2 ...)`

imapping int int ... → imapping

Returns a new imapping with the same associations as *imap*, except
those for keys equal to *n1, n2, ...*.  If an *ni* does not have an
association in *imap*, it is ignored.

`(imapping-delete-all imap ns)`

imapping list[int] → imapping

Returns a new imapping with the same associations as *imap*, except
those for keys equal to an element of *ns*.

`(imapping-update imap n mproc)`

imapping int (\* → maybe[\*]) → imapping

`(imapping-update/key imap n mproc)`

imapping int (n \* → maybe[\*]) → imapping

Returns a new imapping with the same associations as *imap*, except
that the association for *n* is updated as follows.  *mproc* is
applied to the value associated with *n* and is expected to return
a Maybe value.  If it returns Nothing, the association is deleted;
if it returns Just *v*, then *(n, v)* is added to the new imapping.

`imapping-update/key` is the same as `imapping-update`, except that
*mproc* is called on *n* and its associated value, in that order.

Simple versions of several other update operations may be defined
in terms of `imapping-update`, e.g.:

    (imapping-delete imap n)
     ≡
    (imapping-update imap n (λ (_) (nothing)))

    (imapping-adjoin imap n v)
     ≡
    (imapping-update imap n (λ (_) (just v)))

`(imapping-alter imap n proc)`

imapping int (maybe \* → maybe \*) → imapping

Returns a new imapping with the same associations as *imap*, except
that the association, or lack thereof, for *n* is updated as follows.
If the association *(n, v)* exists in *imap*, then *proc* is called on
Just *v*; if no such association exists, then *proc* is called on
Nothing.  If the result of this application is Nothing, the
association is deleted (or no new association is added); if the result
is Just *v′*, a new association *(n, v′)* is added to the new
imapping, replacing any old association for *n*.

`imapping-alter` is a very general operator on imappings, and most
of the other update operations may be defined in terms of it.

      (imapping-update imap n f)
    ≡
      (imapping-alter imap n (λ (m)
                               (maybe-ref m
                                          nothing
                                          (λ (v) (f v)))))

`(imapping-delete-min imap)`
`(imapping-delete-max imap)`

imapping → imapping

Returns a new imapping with the same associations as *imap*, except
for the association with the least/greatest key.  If *imap* is empty,
returns an empty imapping.

`(imapping-update-min imap mproc)`
`(imapping-update-max imap mproc)`

imapping (\* → maybe[\*]) → imapping

`(imapping-update-min/key imap mproc)`
`(imapping-update-max/key imap mproc)`

imapping (int \* → maybe[\*]) → imapping

Returns a new imapping with the same associations as *imap*, except
that the association for the least/greatest key *n* is updated as
follows.  *mproc* is applied to the value associated with *n* and is
expected to return a Maybe value.  If it returns Nothing, the
association is deleted; if it returns Just *v*, then *(n, v)* is added
to the new imapping.

`imapping-update-min/key` and `imapping-update-max/key` are the same
as `imapping-update-min` and `imapping-update-max`, respectively,
except that *mproc* is called on *n* and its associated value, in that
order.

# Size

`(imapping-size imap)`

imapping → int

Returns the number of associations in *imap*.

# Traversal

`(imapping-count pred imap)`

(\* → boolean) imapping → int

`(imapping-count/key pred imap)`

(int \* → boolean) imapping → int

Returns the number of associations in *imap* whose values satisfy
*pred*.

`imapping-count/key` is the same, except that *pred* is called on
the key and value of each association.

`(imapping-any? pred imap)`

(\* → boolean) imapping → boolean

Returns `#t` iff there exists an association in *imap* whose value
satisfies *pred*.  *imap* is traversed in ascending numerical order
of keys.

`(imapping-every? pred imap)`

(\* → boolean) imapping → boolean

Returns `#t` iff the value of every association in *imap* satisfies
*pred*, or if *imap* is empty.  *imap* is traversed in ascending
numerical order of keys.

`(imapping-map proc imap)`

(\* → \*) imapping → imapping

`(imapping-map/key proc imap)`

(int \* → \*) imapping → imapping

Returns a new imapping.  For each association *(n, v)* in *imap*,
the association *(n, (proc v))* is added to the new imapping.
Associations are traversed in an arbitrary order.

`imapping-map/key` is the same, except that *proc* is called on
the key and value of each association.

Note that, in contrast to SRFI 146's map procedures, these procedures
transform the values of *imap* only; that is, the set of keys of the
resulting imapping are the same as that of *imap*.

`(imapping-for-each proc imap)`

(\* → \*) imapping → unspecified

`(imapping-for-each/key proc imap)`

(int \* → \*) imapping → unspecified

Calls *proc* on the value of each association in *imap* and returns
an unspecified value.  *imap* in traversed in ascending numerical
order of keys.

`imapping-for-each/key` is the same, except that *proc* is called on
the key and value of each association.

`(imapping-fold-left kons knil imap)`
`(imapping-fold-right kons knil imap)`

(\* \* → \*) \* imapping → \*

`(imapping-fold-left/key kons knil imap)`
`(imapping-fold-right/key kons knil imap)`

(int \* \* → \*) \* imapping → \*

Folds *proc* over *imap*, using *knil* as the base value.
`imapping-fold-left` folds in ascending numerical order of keys;
`imapping-fold-right` folds in descending order.

`imapping-fold-left/key` and `imapping-fold-right/key` are the same
as `imapping-fold-left` and `imapping-fold-right`, respectively,
except that *proc* is also passed the key of each association.

`(imapping-map->list proc imap)`

(\* → \*) imapping → list[\*]

`(imapping-map/key->list proc imap)`

(int \* → \*) imapping → list[\*]

Fusion of `(imapping-values (imapping-map proc imap)`.

`imapping-map/key->list` is the same, except that *proc* is called on
the key and value of each association.
