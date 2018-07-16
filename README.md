# categorial-syntax

Experiments with parsing categorial grammars https://en.wikipedia.org/wiki/Categorial_grammar

Categorial grammars treat words like datatypes. For example, `man : Noun` and `happy : Noun -> Noun`.
This means that a grammar is a map from String to WordType. I think specifying grammars in this way
would make it easier to write a programming language with extensible syntax. 

Currently I have a pretty specialized recognizer for a grammar written in the categorial style, but I have
no idea how to build a parse tree using that algorithm.
