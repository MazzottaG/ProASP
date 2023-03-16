#
CXX = g++

CXXFLAGS := -std=c++17 -Wall -Wextra 

LIB		:= Compiler/lib
ANTLR	:= libantlr4-runtime.a

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
	cp $(REQUIRED_LIB) $(LIB)/$(ANTLR)
	$(CXX) $(CXXFLAGS) $(SRC)/ProAsp.cpp -o dist/proasp