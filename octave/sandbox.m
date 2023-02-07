pkg load communications

clear all
close all

[originalData, txData] = ads_b_tx_gen('8D86D5E058135037C0A9112B72B7');

figure()
subplot(2, 1, 1)
plot(txData)
title("Transmitted Waveform")
hold on
subplot(2, 1, 2)
plot(originalData)
title("Base Message")
