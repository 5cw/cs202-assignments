# Lexi Reinsborough CS202 Final Project Proposal

### Group members:
 - Lexi Reinsborough

### Project features:
  - Goals:
    - Characters 
    - Fixed-length character buffers (Strings)
    - String literals
    - Strings are stack-allocated (untuplable)
    - Printing
    - Indexing (setting and getting per character)
    - ASCII
    - ord(c: char) and chr(i: int)
    - C implementations called from x86
  - Stretch Goals:
    - int(s: str) and str(i: int), bool(s: str) and str(b: bool)
    - Able to be added to tuples.
    - Heap allocation
    - Dynamic String length
    - UTF-8
    - Concatenation
    - String slicing
    - String formatting
    - Native x86 implementation
    - Nullability (Not necessarily related to strings, but I want to give it a try if things are unexpectedly smooth, and also to have something to return on failure to convert things.)

The most scaled back version is one with static length character buffers which can be written to by index and also by string literals. They are stored in the stack and cannot be put into tuples. This would be implemented in a higher-level language and called from x86.

As many of the stretch goals as can be added will be. I don't know how difficult this is going to be, I imagine I'll be able to do at least a few, but we'll see. I think many of them will be accomplishable with the help of higher-level functions, although perhaps I can transplant and modify compiled C code to help me out.

```python
ch = 'c' # single/double quotes distinction if possible.
st = "String" # will be stored as length 6 character buffer
ch = st[5] 
ch = chr(ord(ch) + 1) # basic character manipulation
st[5] = ch
print(st) # will print "Strinh"
st = "Invalid" # will either fail because string is different length or compiler will use longest available and null-terminate.
st = str[10] # will create character buffer with 10 indices with some initialization

# stretch goals:
n = 0
st = ""
while n < 100:
    st = st + str(n) # dynamic length, int conversion, and concatenation

slice = st[0:10] # slicing

t = ("tuple", 'c', 9) # tuples
    

```