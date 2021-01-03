# multi-dispatch

### mm
I've taken from the [@littledan 's repository](https://github.com/littledan/Factor/tree/multimethods/extra/multi-methods) for his pilot implementation of the multiple methods and made a few changes, including making it work with the current Factor, putting the dynamic variable descriptions before the stack inputs, and renaming some things to suit my preferences.

### mm3
Syntax of [`multi-methods`](https://github.com/factor/factor/tree/master/extra/multi-methods) to be the same as mm

### mm5
Dispatching with Caching

### mm6
Generate code similar to the generic word for single dispatch when there is only one specializer

### mm7
Local variables can be used in the definition by `MM::`. Trying to realize `call-next-multi-method`.
