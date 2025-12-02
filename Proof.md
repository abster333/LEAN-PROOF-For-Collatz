Partial Collatz Proof : Why Loop Can’t Exist

Yenya∗

October 2024

**Abstract**

The Collatz Conjecture states given any positve integer, the continues application of the rules 3*x* + 1 when x is odd, and*x* 2 when x is even will eventually reach 1.

*C* : Z *→*Z

*C*(*x*) =3*x* + 1

*x*

2

if *x ≡*1 (mod 2) *,*

if *x ≡*0 (mod 2) *,*

In this paper we show that a sequence of numbers produced from these rules that repeat themselves which I call a loop, cannot exist. The only exception is the sequence 1*,* 4*,* 2*,* 1 *. . .*. To do this, first I define the rules for the reverse Collatz Conjecture.

*C* : Z *→*Z

 *x ·* 2 if *x ≡*1 (mod 2) *,*

*E*

*C*(*x*) = *x ·* 2 if *x ≡*0 (mod 2) *,−→*

Next, I establish that the smallest member of the loop has to be an odd number. Afterwards, I *x −*1 3 if *x ≡*0 (mod 2) *,−→* *O*

show when working in reverse there are three distinct groups of odd numbers. One of these groups, which I call a **Type II** Odd, is a multiple of 3. This group produces a sequence in the reverse direction that can not be reached. The other 2 groups produce a pattern in the reverse that gives us a **Type II** Odd one third of the time. This pattern is formalized with the sum

*n*

2*k−*1

3*k*

*k*=1

The above sum determines the percentage of branches that start with a **Type II** Odd. When we evaluate this sum with a limit as *n →∞*, we get

*n*

2*k−*1

lim = 1

*n→∞k*=1 3*k*

As *n →∞*, the number of branches that start with a **Type II** Odd goes to 1. We take this as meaning that loops cannot form, as there is no way for a sequence to get back to its starting value.

∗Inspired by Dad

1

![](attachment:5c960fd8-dfdb-466c-915c-0859659d458f:image1.png)

![](attachment:d3ea654e-012c-46ef-84ab-a483bab3f057:image2.png)

**1 Definitions**

**1.1** **Collatz Conjecture**

*C* : Z *→*Z

“The 3x + 1 problem, or Collatz problem, is to prove that starting from any positive integer, some *C*(*x*) =



3*x* + 1

*x*

2

if *x ≡*1 (mod 2) *,*

if *x ≡*0 (mod 2) *,*

iterate of this function takes the value to 1” [1].

**1.2** **Reverse Collatz Rules**

*C* : Z *→*Z

 *x ·* 2 if *x ≡*1 (mod 2) *,*

*E*

*C*(*x*) =*x ·* 2 if *x ≡*0 (mod 2) *,−→*

 *x −*1

3 if *x ≡*0 (mod 2) *,−→*

*O*

The reverse rules unlike the normal Collatz rules have three conditions. One for odd numbers, and

two for even numbers. The arrows with the letters above them indicate whether or not an output is

Even(E) or Odd(O).

**1.3** **Collatz Loop Proof Definitions**

- **Collatz Sequence** -A collection of numbers that follow from each other when the Collatz or

Reverse Collatz rules are applied

Figure 1: An example of a sequence for The the Collatz Conjecture where x=7

Figure 2: An example of a sequence for The Reverse Collatz Conjecture.

This Differs from the other example

52 because some Evens(CERS) have 3 paths

1184

34 26 448 149

112

197 592

22 17 224 144

11 296

112 72

7 49 148 56 36

74 28 18

37 14 9

7

2

- **Collatz Loop** - This is a theoretical sequence such that when you start with a positive integer, some iterate of the Collatz function takes the value back to the starting positve integer. Such a sequence would disprove the Collatz Conjecture. This is the case because such a sequence would if the rules of the Collatz Conjecture are applied to the numbers in the sequence would repeat its self, and subsequently never reach 1.
- **Collatz Odd Reachable (COR)** - These are positive odd integers reached from applying the RCR(1.2).

*O*

**Example:** 28*−→*9

In the example above, 9 would be a COR. The arrow with the O above it helps differentiates the two possible operations possible for even numbers when using the RCR(1.2). Of the two it is the operation that produces an odd number.

We can see below that with the normal Collatz rules the opposite sequence can be attained.

9 *→*28

- **Collatz Even Reachable (CER)** - These are positive even integers reached from applying the RCR(1.2), and more specifically, positive even integers that have a valid COR.

*E*

**Example:** 7 *→*14*−→*28

In the example above, 28 would be considered a CER, whereas 14 would not because it does not have a valid COR. When applying the RCR(1.2), 14 produces 13 3 which is not an integer. On the Other hand, applying RCR(1.2) to 28 yields 9.

We can see below that with the normal Collatz rules the opposite sequence can be attained.

28 *→*14 *→*7

- **Collatz Even Unreachable (CEU)** - These are positive even integers reached from applying the RCR(1.2) that do not have a valid COR.

*E*

**Example:** 11 *→*22*−→*44

In the above example, 44 would be considered a CEU whereas 22 would not. The logic is the same as in the example for CERs. We see, 22 would be considered a CER because its output 7 is a valid COR. Conversely, 44 has an output 43 3 , which is not a valid COR because it is not an integer. Therefore, 44 fits the definition of a CEU.

We can see below that with the normal Collatz rules the opposite sequence can be attained.

2811 *→*44 *→*22 *→*7

- **Branch** - Branches exist only for the Reverse Collatz Conjecture. An example of this can be found in Figure 2, for the sequence starting with 7. Immediate results would be considered to be a part of the branch. So, CORS such as 9, 37, and 149 would be a part of the 7 branch. Furthermore 9,37, and 149 are also considered to have their own branch.

a) **Main Branch** - From Figure 2, the branch starting with 7 would be considered the main branch. Whereas the ones starting with 9,37, and 149 would not be considered Main Branches. This is because the branch starting with 7 is the first branch we consider.

3

**2 Basic Proof Criteria**

1. We are looking for a Collatz sequence that fits the definition of a Collatz Loop. Such a sequence would disprove the Collatz Conjecture as long as 1 is not a member of the sequence.

2. If such a sequence does exist the smallest member of said sequence has to be an odd number. This follows from the definition of the conjecture itself. Even numbers produce a number smaller than themselves. Whereas odd number produce a number greater than themselves.

3. There are 3 types of odd numbers in the Collatz world.

(a) **Type I** - Odds that satisfy the equation 1 + 6*m, m ∈*Z+

(b) **Type II** - Odds that satisfy the equation 3 + 6*m, m ∈*Z+

(c) **Type III** - Odds that satisfy the equation 5 + 6*m, m ∈*Z+

4. When working backwards and applying the Reverse Collatz Rules(1.2) **Type II** Odds produce a sequence that has zero CORs to be more precise, a sequence consisting of CEUs

(a) An Example of this is 3 *→*6 *→*12 *. . .*

(b) The starting number in this example of a **Type II** Odd is a multiple of 3. This fact comes from the definition of **Type II** Odds. Proceeding numbers when applying the RCR(1.2) will be even multiples of three. We can see that the *x·*2 rule for evens produces an integer. This is not the case when applying the*x −*1 rule. For even multiples of 3, this rule produces 3

non-integer values. CEUs are defined as even numbers that do not have valid CORs. We can see from our description of the sequences of **Type II** Odds that all the members of the sequences are even numbers with non-integer CORs, or in other words invalid CORs. This is not the case for the other Type of Odds, because they don’t produce even multiples of three when applying the RCR(1.2).

**3 Equations for CORs, CERs, and DCORs**

1. The general formulas for CORs and CERs are

*COR* = 2*n*(*x* + 6*m*) *−*1 = 2*nx −*1 + 2*n*+1*m*

3 3

*CER* = 2*n*(*x* + 6*m*)

*n ∈*Z+, repersents the number of times the *x ·* 2 rule has been applied. *m ∈*Z+ *x* = 1*,* 3*,* 5 is used as a placeholder for the three starting odds. 0, helps define our starting value.

2. The Different Types materialize CORs at different values of *n*. We show this by using the equation for CORs, and by substituting the different values for *x*

(a) **Type I** :

*x* = 1 2*n−*1 + 2*n*+1*m* 3

Valid CORs materialize at even values of *n*

*n* = 2*,* 4*,* 6*,* 8*, . . .*

*n* = 2*k, k ∈*Z+

4

(b) **Type II** :

*x* = 3

2*n*+ 2*n*+1*m −*1

This will never produce a valid COR. From the equation above, it is clear that we will always produce a fractional value because the variables m and n are integers. Since CORs have to be integers, values produced by this equation are not valid.

(c) **Type III** :

*x* = 5

2*n·* 5 *−*1 + 2*n*+1*m* 3

Valid CORs materialize at odd values of *n*

*n* = 1*,* 3*,* 5*,* 7*, . . .*

*n* = 2*k* + 1*,* *k ∈*Z+

3. The Difference between subsequent CORs is equal to the value of the CER of the smaller COR.

*COR*1 = 2*n*(*x* + 6*m*) *−*1

3

*COR*2 = 2*n*+2(*x* + 6*m*) *−*1

3

As we can see from the above equation and from the findings of 3.2.a and 3.2.c, valid CORs

materialize at *n* values that are +2 apart. Figure 2.

This is observer in the pattern that emerges in

*DCOR* = *COR*2 *−COR*1 = 2*n*+2(*x* + 6*m*) *−*1*−*2*n*(*x* + 6*m*) *−*1 = 2*n*(*x* + 6*m*)

As we can see from the above equation, DCOR is equivalent to the smaller CER. Taking and example from Figure 2 the difference between two valid CORs 9 and 37 is 28 which is the CER of the smaller COR, 9. This pattern continues for the main branch, and for branches not starting with a **Type II** Odd. This is shown with the branch starting with 37 which is not a **Type II** Odd. The fact that **Type II** Odds do not produce this pattern is also shown in Figure 2. The branch starting with 9 which is a **Type II** Odd has no valid CORs, and subsequently all of its members are CEUs.

**4 Odd Type Difference Categorization**

1. The three groups of Odd Types have a difference of 2 and 4. Members of the same group have a difference of 6. This can be formalized in the following way.

(a) **Odd Type Difference 1(OTD I)**

*OTD* I : *Xp* = 2 + 6*p, p ∈*Z+ 0*,*

*Xp ≡*2 (mod 6)

The members of this group when added to any of the odd Types will result in an odd that is 1 Type away.

**Example:** 1(Type I) + 2(OTD I) = 3(Type II)

(b) **Odd Type Difference 2(OTD II)**

*OTD* II : *Xp* = 4 + 6*p, p ∈*Z+ 0*,*

*Xp ≡*4 (mod 6)

The members of this group when added to any of the odd Types will result in an odd that is 2 Types away.

**Example:** 1(Type I) + 4(OTD II) = 5(Type III)

5

(c) **Odd Type Difference 3(OTD III)**

*OTD* III : *Xp* = 6*p, p ∈*Z+*,*

*Xp ≡*0 (mod 6)

The members of this group when added to any of the Odd Types will result in an odd of the same Type.

Given the above equations we can group all even numbers into one of the OTD’s.

2. All valid DCORs are in the group OTD II

*DCOR* = 2*n*(*x* + 6*m*)

When determining an OTD group we know the most significant parts are essentially what is left over after dividing by 6. So, we can rewrite the above equation as

2*nx*

(a) **Type I** :

*x* = 1

*n* = 2*k, k ∈*Z+ 4*k*= 4 + 6*p, p ∈*Z+ 4*k≡*4 (mod 6) The above is equivalent to the definition of OTD II.

(b) **Type II** :

*x* = 3

*No valid CORS*

(c) **Type III** :

*x* = 5

*n* = 2*k* + 1*, k ∈*Z+

10 *·* 4*k*= (4 + 6)4*k*= 4*K*+1+ 6 *·* 4*k*

4*k*+1= 4 + 6*p,* *p ∈*Z+

4 + 6*p* + 6(4 + 6*p*) = 4 + 6*p*

10 *·* 4*k≡*4 (mod 6) The above is equivalent to the definition of OTD II.

3. Given that all DCORs are in group OTD II, and by the definition of OTD II, all subsequent CORs are in Odd Types that are two apart ( TYPE I →TYPE III and TYPE III →TYPE II and TYPE II →TYPE I).

This implies that given a starting odd number when we apply the RCR(1.2), subsequent CORs will be of different Odd Type following a specified pattern.

6

**5 Conclusions**

1. From 2.3, we saw that there are 3 Types of Odds with Corresponding equations.

(a) **Type I** - Odds that satisfy the equation 1 + 6*m, m ∈*Z+

(b) **Type II** - Odds that satisfy the equation 3 + 6*m, m ∈*Z+

(c) **Type III** - Odds that satisfy the equation 5 + 6*m, m ∈*Z+

2. In 2.4 and 3.2.b, I showed that **Type II** Odds create branches that are unreachable, or in other words, branches consisting of CEUs.

3. In 3.3, I defined the equation for a DCOR

*DCOR* = 2*n*(*x* + 6*m*)

*n ∈*Z+

*m ∈*Z+ *x* = 1*,* 3*,* 5

4. In 4.1, I defined the three groups of possible differences between the three Odd Types, which are referred to as Odd Type Difference.

(a) **Odd Type Difference 1(OTD I)**

*OTD* I : *Xp* = 2 + 6*p, p ∈*Z+ 0*, Xp ≡*2 (mod 6)

The members of this group, when added to any of the odd Types, will result in an odd that is 1 Type away.

(b) **Odd Type Difference 2(OTD II)**

*OTD* II : *Xp* = 4 + 6*p, p ∈*Z+ 0*, Xp ≡*4 (mod 6)

The members of this group, when added to any of the odd Types, will result in an odd that is 2 Types away.

(c) **Odd Type Difference 2(OTD III)**

*OTD* III : *Xp* = 6*p, p ∈*Z+*, Xp ≡*0 (mod 6)

The members of this group, when added to any of the Odd Types, will result in an odd of the same Type.

5. In 4.2, I showed that all valid DCORs are in **Odd Type Difference 2(OTD II)**. This implies that subsequent CORs are differnt Odd Types. The change from one Odd Type to another follows a pattern, this pattern can be found below

( TYPE I →TYPE III and TYPE III →TYPE II and TYPE II →TYPE I)

6. Given that the COR Type changes every single time, a third of the Cors in the main branch are observed to be of Type II, meaning that they are unreachable.

7. For the 2 3 of the CORs that are not Type II Odds we know that those branches will also produce the same pattern. Meaning 1 3 of their CORs will be Type II Odds. We can formalize this with the sum

*n*

2*k−*1

3*k*

*n ∈*Z+ *k*=1

*n* represents the number of branches we are considering

The above sum gives the percentage of CORs that are Type II Odds.

7

8. The limit of this sum as *n →∞*is

*n*

2*k−*1 lim = 1 *n→∞k*=1 3*k*

From this, we conclude that all branches will eventually terminate with a COR that is a Type

II Odd.

8

**References**

[1] Jeffrey C. Lagarias. The 3x+1 problem: An annotated bibliography (1963–1999) (sorted by author), 2011.

9