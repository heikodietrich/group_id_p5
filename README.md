This is the pre-release GAP code accompanying the paper

  "Group identification for the groups of order dividing $p^5$" (arxiv: TBA)

by Heiko Dietrich, Bettina Eick, and Henrik Schanze.

Eventually this code will be distributed with a future release of GAP (TBA).

Main file: Idp5.g

Once loaded, the code provides a method `IdSmallGroup` for input groups that are $p$-groups of order dividing $p^5$ where $p$ is any prime. It returns the ID as defined in the `SmallGroups Library`.

The code also defines an attribute `IsomorphismSmallGroup` and provides a method for the groups considered here: for an input group G it computes an isomorphism $G\to \text{SmallGroup}(\text{IdSmallGroup}(G))$.

The test function `TestSmallGroupId_p5` takes as input a list `lps` of primes, an integer `nr`, and a Boolean `testIso`; it will then run over `nr` copies of groups of order $p^i$ where $p$ lies in `lps` and $i\in\{1,2,3,4,5\}$ and tests that `IdSmallGroup` is computed correctly. If the Boolean `testIso` is true, then it also tests the isomorphism construction. It outputs statistics of the runtimes.

Example:

```gap
gap> ### get random group
gap> R := SmallGroup(7^5,65);;
gap> R := Image(IsomorphismPermGroup(R));;
gap> repeat gens := List([1..8],x->Random(R)); until Group(gens)=R;;
gap> R := Group(gens);;
gap> R := Image(IsomorphismPcGroup(R));;
gap>
gap> ### construct ID
gap> IdSmallGroup(R);
[ 16807, 65 ]
gap>
gap> ### get iso to standard copy
gap> iso := IsomorphismSmallGroup(R);;
gap>
gap> ### Image(iso) is canonically isomorphic to SmallGroup(7^5,65)
gap> ### but a different GAP object; demonstrate isomorphism to
gap> ### another library copy
gap> H := SmallGroup(7^5,65);;
gap> isoRtoH := iso * GroupHomomorphismByImages(Image(iso),H,Pcgs(Image(iso)),Pcgs(H));;
gap> Source(isoRtoH)=R and Image(isoRtoH)=H and IsBijective(isoRtoH);
true
```
