# Bordeaux

One of the great features of the [Alloy Analyzer](http://alloy.mit.edu) is that it can
produce examples illustrating the meaning of the user's model. These
*inside-the-box* examples, which are formally permissible but (potentially)
undesirable, help the user understand *under-constraint* bugs in the model.
To get similar help with *over-constraint* bugs in the model the user needs
to see examples that are desirable but formally excluded: that is, they
need to see *outside-the-box* examples (otherwise known as near-miss examples
in the AI literature). We have developed a prototype extension of
the Alloy Analyzer, named Bordeaux, that can find these examples that
are near the border of what is permitted, and hence might be desirable.
More generally, Bordeaux finds a pair of examples, *a*, *c*, at a minimum
distance to each other, and where a satisfies model *A* and *c* satisfies model
*C*. The primary use case described is when model *C* is the negation of
model *A*, but there are also other uses for this relative minimization. Previous
works, such as Aluminum, have focused on finding inside-the-box
examples that are absolutely minimal.

## Design and experiemnts

Please read: [Bordeaux: A Tool for Thinking Outside the Box](https://goo.gl/CHa9Qv)
