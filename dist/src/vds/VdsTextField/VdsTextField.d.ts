import { InputProps as MuiInputProps } from '@mui/material/Input';
import * as React from 'react';
export declare type InputProps = {
    label?: string;
    helperText?: string;
    type?: string;
    errorText?: string;
} & MuiInputProps;
export declare const VdsTextField: React.VFC<InputProps>;
