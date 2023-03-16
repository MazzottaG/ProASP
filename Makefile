#
CXX = g++

CXXFLAGS := -std=c++17 -Wall -Wextra 

LIB		:= Compiler/lib
ANTLR	:= libantlr4-runtime.a
GLUCOSE_GEN_SRC	:= glucose-4.2.1/sources/simp/generators
GLUCOSE_PROP_SRC	:= glucose-4.2.1/sources/simp/propagators

SRC 	:= .
REQUIRED_LIB	:= $(LIB)/linux-$(ANTLR)
ifeq ($(OS),Windows_NT)
		
else
	UNAME_S := $(shell uname -s)
	ifeq ($(UNAME_S),Darwin)
		REQUIRED_LIB	:= $(LIB)/macos-$(ANTLR)
	endif
endif

compile:
	if [ ! -d "$(GLUCOSE_GEN_SRC)" ]; then \
        mkdir $(GLUCOSE_GEN_SRC); \
    fi
	if [ ! -d "$(GLUCOSE_PROP_SRC)" ]; then \
        mkdir $(GLUCOSE_PROP_SRC); \
    fi
	
	cp $(REQUIRED_LIB) $(LIB)/$(ANTLR)
	$(CXX) $(CXXFLAGS) $(SRC)/ProAsp.cpp -o dist/proasp