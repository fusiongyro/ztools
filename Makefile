all: zt2zu

zt2zu: foo.l
	flex foo.l
	$(CC) -o $@ lex.yy.c
