import Alert from '@mui/material/Alert';
import { withStyles } from '@mui/styles';

export const VdsAlert = withStyles(() => ({
  root: {
    backgroundColor: '#FFFFFF',
    color: '005075',
    borderRadius: 'unset',
    fontFamily: 'Roboto',
    fontWeight: '400',
    fontSize: '16px',
  },
  standardInfo: {
    border: `1px solid #005075`,
    color: '#005075',
    borderBottom: `3px solid #005075`,
    '& .MuiAlert-icon': {
      fill: '#005075'
    },
    '& svg': {
      fill: '#005075'
    }
  },
  standardSuccess: {
    border: `1px solid #09822A`,
    borderBottom: `3px solid #09822A`,
    color: '#09822A',
    '& .MuiAlert-icon': {
      fill: '#09822A'
    },
    '& svg': {
      fill: '#09822A'
    }
  },
  standardWarning: {
    border: `1px solid #FDB927`,
    borderBottom: `3px solid #FDB927`,
    color: '#FDB927',
    '& .MuiAlert-icon': {
      fill: '#FDB927'
    },
    '& svg': {
      fill: '#FDB927'
    }
  },
  standardError: {
    border: `1px solid #D82829`,
    borderBottom: `3px solid #D82829`,
    color: '#D82829',
    '& .MuiAlert-icon': {
      fill: '#D82829'
    },
    '& svg': {
      fill: '#D82829'
    }
  }
}))(Alert);
