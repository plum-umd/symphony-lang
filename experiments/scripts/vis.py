#!/usr/local/bin/python3

import pandas as pd
import matplotlib as mpl
import matplotlib.pyplot as plt

def style():
    mpl.rcParams['font.size']        = 16
    mpl.rcParams['lines.linewidth']  = 2
    mpl.rcParams['lines.markersize'] = 9
    mpl.rcParams['legend.fontsize']  = 10

styles = { ('symphony','lwz', 'rep')    : ('o', 'dashed', 'red', 'LWZ, Replicated'),
           ('symphony','lwz', 'gmw')    : ('o', 'solid', 'purple', 'LWZ, GMW'),
           ('symphony','waksman','rep') : ('o', 'dashed', 'brown', 'Waksman, Replicated'),
           ('symphony','waksman','gmw') : ('o', 'solid', 'blue', 'Waksman, GMW') }

def plot_bench(df):
    fig, ax = plt.subplots()
    for col in df.columns:
        (marker, ls, color, label) = styles[col]
        df[col].plot(title = 'LWZ vs. Waksman', xlabel = "Input Size", ylabel = "Elapsed Time (ms)", marker=marker, linestyle=ls, color=color, label=label, ax=ax)

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
    df = pd.read_csv('lwz_vs_waksman.csv')
    df = df.groupby(['language', 'program', 'protocol', 'inputs']).mean()
    df = df.reset_index(level = ['language', 'program', 'protocol'])
    df = df.pivot(columns = ['language', 'program', 'protocol'], values = 'time')
    plot_bench(df)
    plt.savefig('shuffle.png', bbox_inches='tight', dpi=300)
    legend()

if __name__ == "__main__":
    main()
