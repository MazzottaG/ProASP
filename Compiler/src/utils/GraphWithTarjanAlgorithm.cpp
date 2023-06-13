/*
 *
 *  Copyright 2021  BLIND.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *    http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 */
/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   GraphWithTarjanAlgorithm.cpp
 * Author: alessandro
 * 
 * Created on March 12, 2017, 6:44 PM
 */

#include "GraphWithTarjanAlgorithm.h"

using namespace std;

void GraphWithTarjanAlgorithm::addNode(unsigned int v) {
    if (v >= adj.size())
        for (unsigned int i = adj.size(); i <= v; i++)
            adj.push_back(list<int>());
}
bool GraphWithTarjanAlgorithm::existsEdge(unsigned int v, unsigned int w) {
    if(v >= adj.size()) return false;
    for(list<int>::const_iterator it=adj[v].begin(); it != adj[v].end(); it++ ){
        if(w == *it) return true;
    }
    return false;
}
void GraphWithTarjanAlgorithm::addEdge(unsigned int v, unsigned int w) {
    if (v >= adj.size() || w >= adj.size()) {
        if (v >= w)
            for (unsigned int i = adj.size(); i <= v; i++)
                adj.push_back(list<int>());
        else
            for (unsigned int i = adj.size(); i <= w; i++)
                adj.push_back(list<int>());
    }
    adj[v].push_back(w);
}

// A recursive function that finds and prints strongly connected
// components using DFS traversal
// u --> The vertex to be visited next
// disc[] --> Stores discovery times of visited vertices
// low[] -- >> earliest visited vertex (the vertex with minimum
//             discovery time) that can be reached from subtree
//             rooted with current vertex
// *st -- >> To store all the connected ancestors (cthisould be part
//           of SCC)
// stackMember[] --> bit/index array for faster check whether
//                  a node is in stack

void GraphWithTarjanAlgorithm::SCCUtil(int u, int disc[], int low[], stack<int>& st,
        bool stackMember[], vector< vector <int> > & scc) {
    // A static variable is used for simplicity, we can avoid use
    // of static variable by passing a pointer.
    static int time = 0;

    // Initialize discovery time and low value
    disc[u] = low[u] = ++time;
    st.push(u);
    stackMember[u] = true;

    // Go through all vertices adjacent to this
    list<int>::iterator i;
    for (i = adj[u].begin(); i != adj[u].end(); ++i) {
        int v = *i; // v is current adjacent of 'u'

        // If v is not visited yet, then recur for it
        if (disc[v] == -1) {
            SCCUtil(v, disc, low, st, stackMember, scc);

            // Check if the subtree rooted with 'v' has a
            // connection to one of the ancestors of 'u'
            // Case 1 (per above discussion on Disc and Low value)
            low[u] = min(low[u], low[v]);
        }            // Update low value of 'u' only of 'v' is still in stack
            // (i.e. it's a back edge, not cross edge).
            // Case 2 (per above discussion on Disc and Low value)
        else if (stackMember[v] == true)
            low[u] = min(low[u], disc[v]);
    }

    // head node found, pop the stack and print an SCC
    int w = 0; // To store stack extracted vertices
    if (low[u] == disc[u]) {
        int currentSCCIndex = scc.size();
        scc.push_back(vector<int>());
        while (st.top() != u) {
            w = (int) st.top();
            scc[currentSCCIndex].push_back(w);
//            cout << w << " ";
            stackMember[w] = false;
            st.pop();
        }
        w = (int) st.top();
//        cout << w << "\n";
        scc[currentSCCIndex].push_back(w);
        stackMember[w] = false;
        st.pop();
    }
}

// The function to do DFS traversal. It uses SCCUtil()

const vector< vector <int> > GraphWithTarjanAlgorithm::SCC() {
    int disc[adj.size()];
    int low[adj.size()];
    bool stackMember [adj.size()];
    stack<int> st;

    vector< vector <int> > scc;

    // Initialize disc and low, and stackMember arrays
    for (unsigned int i = 0; i < adj.size(); i++) {
        disc[i] = NIL;
        low[i] = NIL;
        stackMember[i] = false;
    }

    // Call the recursive helper function to find strongly
    // connected components in DFS tree with vertex 'i'
    for (unsigned int i = 0; i < adj.size(); i++)
        if (disc[i] == NIL)
            SCCUtil(i, disc, low, st, stackMember, scc);

    return scc;
}

