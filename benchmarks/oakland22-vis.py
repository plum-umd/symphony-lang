#!/usr/local/bin/python3

import pandas as pd
import matplotlib as mpl
import matplotlib.pyplot as plt

def style():
    mpl.rcParams['font.size']        = 16
    mpl.rcParams['lines.linewidth']  = 2
    mpl.rcParams['lines.markersize'] = 9
    mpl.rcParams['legend.fontsize']  = 10

names = { 'hamming'       : 'Hamming Distance',
          'bio-matching'  : 'Biometric Matching',
          'db-analytics'  : 'DB Analytics',
          'gcd-gc'        : 'Euclid\'s GCD Algorithm',
          'edit-distance' : 'Edit Distance' }

styles = { ('allyn','LAN','plain')  : ('o', 'dashed', 'red', 'Symphony, Plain on LAN'),
           ('allyn','LAN','yao')    : ('o', 'solid', 'purple', 'Symphony, Yao on LAN'),
           ('allyn','WAN','yao')    : ('o', 'dotted', 'brown', 'Symphony, Yao on WAN'),
           ('oblivc','LAN','plain') : ('^', 'dashed', 'blue', 'OblivC, Plain on LAN'),
           ('oblivc','LAN','yao')   : ('^', 'solid', 'orange', 'OblivC, Yao on LAN'),
           ('oblivc','WAN','yao')   : ('^', 'dotted', 'green', 'OblivC, Yao on WAN') }

def plot_bench(bench, df):
    fig, ax = plt.subplots()
    for col in df.columns:
        (marker, ls, color, label) = styles[col]
        df[col].plot(title = names[bench], ylabel = "Elapsed Time (s)", marker=marker, linestyle=ls, color=color, label=label, ax=ax)

def legend():
    fig,ax = plt.subplots()
    leg = plt.figure('Legend')
    for (marker, ls, color, label) in styles.values():
        ax.plot([], marker=marker, linestyle=ls, color=color, label=label)
    handles, labels = ax.get_legend_handles_labels()
    leg.legend(handles, labels, markerscale=.75, handlelength=3.5, loc='center')
    leg.savefig('legend.png', bbox_inches='tight', dpi=300)
    plt.close()
    plt.close()

def main():
    style()
    df = pd.read_csv('end-to-end-final.csv')
    for bench, df in df.groupby('Benchmark'):
        df = df.groupby(['MPC Implementation', 'Network', 'Protocol', 'Input Size']).mean()
        df = df.reset_index(level = ['MPC Implementation', 'Network', 'Protocol'])
        df = df.pivot(columns = ['MPC Implementation', 'Network', 'Protocol'], values = 'Elapsed Time (s)')
        plot_bench(bench, df)
        plt.savefig('{0}.png'.format(bench), bbox_inches='tight', dpi=300)
    legend()

if __name__ == "__main__":
    main()
