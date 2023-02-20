pkg load communications

clear all
close all

[originalData, txData] = ads_b_tx_gen('8D86D5E058135037C0A9112B72B7');

figure()
ax(2) = subplot(2, 1, 2);
plot(txData)
title("Transmitted Waveform")
hold on
ax(1) = subplot(2, 1, 1);
plot(originalData)
title("Base Message")
linkaxes(ax, 'x')
