#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# Copyright (C) 2018  Mate Soos
#
# This program is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License
# as published by the Free Software Foundation; version 2
# of the License.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
# 02110-1301, USA.

import pandas as pd
import numpy as np
import matplotlib.pyplot as plt


def write_mit_header(f):
    f.write("""/******************************************
Copyright (c) 2018, Mate Soos

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
***********************************************/\n\n""")

def add_computed_features_clustering(df):
    print("Adding computed clustering features...")

    todiv = []
    for x in list(df):
        if "szfeat_cur" in x and "std" not in x and "min" not in x and "mean" not in x and "_per_" not in x and x[-3:] != "var" and "binary" not in x:
            todiv.append(x)

    # relative data
    cols = list(df)
    for col in cols:
        if "szfeat_cur" in col:
            for divper in todiv:
                df["("+col+"/"+divper+")"] = df[col]/df[divper]
                df["("+col+"<"+divper+")"] = (df[col] < df[divper]).astype(int)

    print("Added computed features.")


# to check for too large or NaN values:
def check_too_large_or_nan_values(df, features):
    print("Checking for too large or NaN values...")
    # features = df.columns.values.flatten().tolist()
    index = 0
    for index, row in df[features].iterrows():
        for x, name in zip(row, features):
            try:
                np.isfinite(x)
            except:
                print("Name:", name)
                print("Prolbem with value:", x)
                print(row)

            if not np.isfinite(x) or x > np.finfo(np.float32).max:
                print("issue with data for features: ", name, x)
            index += 1

    print("Checking finished.")


def print_confusion_matrix(cm, classes,
                           normalize=False,
                           title='Confusion matrix',
                           cmap=plt.cm.Blues):
    """
    This function prints and plots the confusion matrix.
    Normalization can be applied by setting `normalize=True`.
    """
    if normalize:
        cm = cm.astype('float') / cm.sum(axis=1)[:, np.newaxis]
    print(title)

    np.set_printoptions(precision=2)
    print(cm)


def calc_min_split_point(df, min_samples_split):
    split_point = int(float(df.shape[0])*min_samples_split)
    if split_point < 10:
        split_point = 10
    print("Minimum split point: ", split_point)
    return split_point


def conf_matrixes(self, data, features, to_predict, clf, toprint="test"):
    # get data
    X_data = data[features]
    y_data = data[to_predict]
    print("Number of elements:", X_data.shape)
    if data.shape[0] <= 1:
        print("Cannot calculate confusion matrix, too few elements")
        return 0, 0, 0

    # Preform prediction
    y_pred = clf.predict(X_data)

    # calc acc, precision, recall
    accuracy = sklearn.metrics.accuracy_score(
        y_data, y_pred)
    precision = sklearn.metrics.precision_score(
        y_data, y_pred, pos_label="OK", average="binary")
    recall = sklearn.metrics.recall_score(
        y_data, y_pred, pos_label="OK", average="binary")
    print("%s prec : %-3.4f  recall: %-3.4f accuracy: %-3.4f" % (
        toprint, precision, recall, accuracy))

    # Plot confusion matrix
    cnf_matrix = sklearn.metrics.confusion_matrix(
        y_true=y_data, y_pred=y_pred)
    helper.print_confusion_matrix(
        cnf_matrix, classes=clf.classes_,
        title='Confusion matrix, without normalization (%s)' % toprint)
    helper.print_confusion_matrix(
        cnf_matrix, classes=clf.classes_, normalize=True,
        title='Normalized confusion matrix (%s)' % toprint)

    return precision, recall, accuracy


def calc_greedy_best_features(top_feats):
    best_features = [top_feats[0]]
    for i in range(options.get_best_topn_feats-1):
        print("*** Round %d Best feature set until now: %s"
              % (i, best_features))

        best_sum = 0.0
        best_feat = None
        feats_to_try = [i for i in top_feats if i not in best_features]
        print("Will try to get next best from ", feats_to_try)
        for feat in feats_to_try:
            this_feats = list(best_features)
            this_feats.append(feat)
            print("Trying feature set: ", this_feats)
            mysum = self.one_classifier(this_feats, "x.class", True)
            print("Reported mysum: ", mysum)
            if mysum > best_sum:
                best_sum = mysum
                best_feat = feat
                print("-> Making this best accuracy")

        print("*** Best feature for round %d was: %s with mysum: %lf"
              % (i, best_feat, mysum))
        best_features.append(best_feat)

        print("\n\n")
        print("Final best feature selection is: ", best_features)

    return best_features


def clear_data_from_str(df):
    values2nums = {'luby': 0, 'glue': 1, 'geom': 2}
    df.loc[:, ('cl.cur_restart_type')] = \
        df.loc[:, ('cl.cur_restart_type')].map(values2nums)

    df.loc[:, ('rdb0.cur_restart_type')] = \
        df.loc[:, ('rdb0.cur_restart_type')].map(values2nums)

    df.loc[:, ('rst_cur.restart_type')] = \
        df.loc[:, ('rst_cur.restart_type')].map(values2nums)

    if "rdb1.cur_restart_type" in df:
        df.loc[:, ('rdb1.cur_restart_type')] = \
            df.loc[:, ('rdb1.cur_restart_type')].map(values2nums)

    df.fillna(0, inplace=True)


def filter_min_avg_dump_no(df, min_avg_dumpno):
    print("Filtering to minimum average dump_no of {min_avg_dumpno}...".format(
        min_avg_dumpno=min_avg_dumpno))
    print("Pre-filter number of datapoints:", df.shape)
    df_nofilter = df.copy()

    df['rdb0.dump_no'].replace(['None'], 0, inplace=True)
    df.fillna(0, inplace=True)
    # print(df[["fname", "sum_cl_use.num_used"]])
    files = df[["fname", "rdb0.dump_no"]].groupby("fname").mean()
    fs = files[files["rdb0.dump_no"] >= min_avg_dumpno].index.values
    filenames = list(fs)
    print("Left with {num} files".format(num=len(filenames)))
    df = df[df["fname"].isin(fs)].copy()

    print("Post-filter number of datapoints:", df.shape)
    return df_nofilter, df

def output_to_classical_dot(clf, features, fname):
    sklearn.tree.export_graphviz(clf, out_file=fname,
                                 feature_names=features,
                                 class_names=clf.classes_,
                                 filled=True, rounded=True,
                                 special_characters=True,
                                 proportion=True)
    print("Run dot:")
    print("dot -Tpng {fname} -o {fname}.png".format(fname=fname))
    print("gwenview {fname}.png".format(fname=fname))

def output_to_dot(df2, clf, features, to_predict, name, df):
    import dtreeviz.trees
    X_train = df2[features]
    y_train = df2[to_predict]

    values2nums = {'OK': 1, 'BAD': 0}
    y_train = y_train.map(values2nums)
    print("clf.classes_:", clf.classes_)


    #try:
    viz = dtreeviz.trees.dtreeviz(
        clf, X_train, y_train, target_name=name,
        feature_names=features, class_names=list(clf.classes_))
    viz.view()
    #except:
        #print("It doesn't have both OK or BAD -- it instead has:")
        #print("y_train head:", y_train.head())
    del df
    del df2

    if options.show:
        plt.figure()
        plt.imshow(cm, interpolation='nearest', cmap=cmap)
        plt.title(title)
        plt.colorbar()
        tick_marks = np.arange(len(classes))
        plt.xticks(tick_marks, classes, rotation=45)
        plt.yticks(tick_marks, classes)

        fmt = '.2f' if normalize else 'd'
        thresh = cm.max() / 2.
        for i, j in itertools.product(range(cm.shape[0]), range(cm.shape[1])):
            plt.text(j, i, format(cm[i, j], fmt),
                     horizontalalignment="center",
                     color="white" if cm[i, j] > thresh else "black")

        plt.tight_layout()
        plt.ylabel('True label')
        plt.xlabel('Predicted label')


def print_feature_ranking(clf, X_train, top_num_features, plot=False):
    best_features = []
    importances = clf.feature_importances_
    std = np.std(
        [tree.feature_importances_ for tree in clf.estimators_], axis=0)
    indices = np.argsort(importances)[::-1]
    indices = indices[:top_num_features]
    myrange = min(X_train.shape[1], top_num_features)

    # Print the feature ranking
    print("Feature ranking:")

    for f in range(myrange):
        print("%-3d  %-55s -- %8.4f" %
              (f + 1, features[indices[f]], importances[indices[f]]))
        best_features.append(features[indices[f]])

    # Plot the feature importances of the clf
    if plot:
        plot_feature_importances(importances, indices, myrange)

    return best_features


def plot_feature_importances(importances):
        plt.figure()
        plt.title("Feature importances")
        plt.bar(range(myrange), importances[indices],
                color="r", align="center",
                yerr=std[indices])
        plt.xticks(range(myrange), [features[x]
                                    for x in indices], rotation=45)
        plt.xlim([-1, myrange])
