import { styled } from '@mui/material';
import MuiInput, { InputProps as MuiInputProps } from '@mui/material/Input';
import * as React from 'react';
import { AiFillMinusCircle } from 'react-icons/ai';

export type InputProps = {
    label?: string,
    helperText?: string,
    type?: string,
    errorText?: string,
} & MuiInputProps;

const StyledTextFieldContainer = styled('div')(() => ({
    'display': 'flex',
    'minHeight': '96px',
    'fontFamily': '-apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Oxygen-Sans, Ubuntu, Cantarell, "Helvetica Neue", sans-serif',
    'flexDirection': 'column',
    'width': 'initial',
    'input': { padding: '0 !important' }
}));

const StyledInfosContainer = styled('div')({
    'marginBottom': '12px',
    'display': 'flex',
    'flexDirection': 'column'
});

const StyledHelperTextContainer = styled('span')(({ disabled }: Partial<InputProps>) => ({
    'fontSize': "12px",
    'color': disabled ? '#C1C1C4' : "#9DA6AD",
    'lineHeight': "18px",
    'fontFamily': "Roboto",
    'fontWeight': 400,
    'textAlign': "left"
}));

const StyledLabelContainer = styled('span')(({ disabled, readOnly }: Partial<InputProps>) => ({
    'fontSize': "14px",
    'color': readOnly ? "black" : disabled ? "#9DA6AD" : "#152935",
    'letterSpacing': "0",
    'lineHeight': "18px",
    'fontFamily': "Roboto",
    'fontWeight': 500,
    'textAlign': "left",
    'marginBottom': '8px'
}));

const StyledInput = styled(MuiInput, { shouldForwardProp: (props: any) => props } as any)(({ disabled, readOnly, error }: any) => ({
    'border': disabled ? '1px solid #C1C1C4' : readOnly ? '1px solid #C1C1C4' : error ? '1px solid #D82829' : '1px solid #C9D9E8',
    'backgroundColor': (disabled || readOnly) ? '#FAFBFD' : '#F2F5F8',
    'padding': '7.5px 14px!important',
    'font': 'unset',
    'cursor': disabled ? 'not-allowed!important' : 'text!important',
    '*': {
        'cursor': disabled ? 'not-allowed!important' : 'text!important'
    },
    ':hover': {
        'border': disabled ? '1px solid #0090D1' : readOnly ? '1px solid #C1C1C4' : error ? '1px solid #D82829' : '1px solid #0090D1!important'
    },
    '::placeholder': {
        'fontSize': "14px!important",
        'color': (disabled || readOnly) ? "#C1C1C4" : "#9DA6AD",
        'lineHeight': "18px",
        'fontFamily': "Roboto",
        'fontWeight': 400,
        'textAlign': "left"
    },
    '::before': {
        'all': 'unset'
    },
    '::after': {
        'all': 'unset'
    }
}));

const StyledErrorContainer = styled('span')({
    'fontSize': "12px",
    'color': "#D82829",
    'lineHeight': "18px",
    'fontWeight': 400,
    display: 'flex',
    alignItems: 'center',
    'textAlign': "left"
});

function htmlToText(html: any) {
    var temp = document.createElement('div');
    temp.innerHTML = html;
    return temp.textContent;
}

export const VdsTextField: React.VFC<InputProps> = (props) => {

    const {
        label,
        placeholder,
        errorText,
        readOnly,
        disabled,
        helperText,
        value,
        onChange,
        onKeyPress,
        error,
    } = props;

    return (
        <StyledTextFieldContainer>
            {(label || helperText) && (
                <StyledInfosContainer>
                    {label && (
                        <StyledLabelContainer>
                            {label}
                        </StyledLabelContainer>
                    )}
                    {helperText && (
                        <StyledHelperTextContainer disabled={props?.disabled}>
                            {helperText}
                        </StyledHelperTextContainer>
                    )}
                </StyledInfosContainer>
            )}
            <StyledInput
                value={htmlToText(value)}
                placeholder={placeholder}
                disabled={disabled}
                readOnly={readOnly}
                error={error}
                onChange={onChange}
                onKeyPress={onKeyPress}
            />
            {error && (
                <StyledErrorContainer>
                    <AiFillMinusCircle style={{ fill: '#D82829', fontSize: '13px', padding: '0 5px' }}/> {errorText}
                </StyledErrorContainer>
            )}
        </StyledTextFieldContainer>
    );
}
