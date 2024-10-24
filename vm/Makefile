all: macc

%.o: CFLAGS+= -Wall -pedantic
# macc: LDLIBS +=-lgc
macc: LDLIBS +=-lgc -I/opt/homebrew/Cellar/bdw-gc/8.2.8/include -L/opt/homebrew/Cellar/bdw-gc/8.2.8/lib

clean:
	rm -f *.o macc

.PHONY: clean all
