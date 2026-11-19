#!/usr/bin/env python3
"""Reproducible vector graph atlas to accompany Figure 5.
Usage: python figures/generate_atlas.py (from manuscript folder or anywhere).
"""
from pathlib import Path
import networkx as nx
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle

DIR=Path(__file__).resolve().parent
palette={'edge':'#384D5A','ordinary':'#117A75','exception':'#B24A43','background':'#F9FBFC'}
allg=[g for g in nx.graph_atlas_g() if len(g)<=5]
groups={n:[g for g in allg if len(g)==n] for n in range(6)}
assert [len(groups[n]) for n in range(6)]==[1,1,2,4,11,34]
fig=plt.figure(figsize=(13.0,8.25),facecolor='white')
fig.text(.035,.963,'Complete graph atlas',fontsize=17,weight='bold',color=palette['edge'])
fig.text(.035,.928,'One miniature per unlabelled simple graph, n ≤ 5; red outline marks the unique P₅ exception',fontsize=9,color=palette['edge'])
# 19 classes for n<=4 on left, 34 classes for n=5 on right.
sections=[('n = 0–4 : 19 classes', [g for n in range(5) for g in groups[n]],.026,.36,4,5),('n = 5 : 34 classes',groups[5],.40,.575,7,5)]
for title,graphs,x0,w,cols,rows in sections:
    fig.text(x0,.881,title,fontsize=11,weight='bold',color=palette['edge'])
    top=.846; bottom=.071; cellw=w/cols; cellh=(top-bottom)/rows
    for idx,g in enumerate(graphs):
        col=idx%cols; row=idx//cols
        x=x0+col*cellw; y=top-(row+1)*cellh
        ax=fig.add_axes([x+.003,y+.008,cellw-.006,cellh-.020])
        ax.axis('off')
        is_p5=len(g)==5 and nx.is_isomorphic(g,nx.path_graph(5))
        if is_p5:
            for edge in ax.spines.values(): edge.set_visible(True)
            ax.add_patch(Rectangle((0,0),1,1,transform=ax.transAxes,fill=False,lw=1.9,edgecolor=palette['exception']))
        if len(g):
            if is_p5:
                matcher=nx.isomorphism.GraphMatcher(g,nx.path_graph(5))
                assert matcher.is_isomorphic()
                p=matcher.mapping
                order=sorted(g.nodes(),key=lambda u:p[u])
                pos={u:(j-.5*(len(g)-1),0.04*((-1)**j)) for j,u in enumerate(order)}
            else:
                pos=nx.spring_layout(g,seed=41,iterations=55)
                if len(g)==1: pos={next(iter(g.nodes())):(0,0)}
            nx.draw_networkx_edges(g,pos,ax=ax,width=1.2,edge_color=palette['edge'])
            nx.draw_networkx_nodes(g,pos,ax=ax,node_size=40,node_color=(palette['exception'] if is_p5 else palette['ordinary']),edgecolors='white',linewidths=.5)
        g_n=len(g); k=groups[g_n].index(g)
        ax.set_title(f'{g_n}.{k+1}' + ('  P₅' if is_p5 else ''),loc='left',fontsize=7,color=(palette['exception'] if is_p5 else palette['edge']),pad=1)
fig.text(.035,.02,'Green/teal: EGU     Red: P₅ non-EGU     Layouts are schematic; graph identities are certified by isomorphism checks.',fontsize=8,color=palette['edge'])
fig.savefig(DIR/'atlas.pdf',format='pdf',bbox_inches='tight',pad_inches=.12)
print('created',DIR/'atlas.pdf')