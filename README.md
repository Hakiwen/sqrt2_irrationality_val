Comparison of outputs between Claude and GPT4 chats on the following prompt:

`Can you give me a coq proof that the square root of two is irrational, and that will compile.`

The solution comes from [io12](https://github.com/io12) in [coq-proofs](https://github.com/io12/coq-proofs/tree/master)
Tested by running `coqc [model].v` and checking for a successful compilation.

So far, none have single-shot generated a successful prompt.

# UPDATE 2024-03-05

With the release of Claude 3, I've added an additional response from Claude 3 Sonnet. It does not compile.

I hope to update this with future attempts.

# UPDATE 2024-09-13

Added o1 (using o1-preview), did not compile.
