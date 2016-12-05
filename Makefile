default:
	alex src/Lang/Lexer.x
	happy src/Lang/Parser.y
	cabal build
